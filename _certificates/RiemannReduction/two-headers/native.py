"""Compile the consolidated project root with no removed or superseded object on Lean's path."""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "reflection-imports"))
from rebuild import FLAGS, TARGETS
from trim import project_file

def main():
    p = argparse.ArgumentParser(description=__doc__)
    for arg in ("source", "objects", "work"):
        p.add_argument(arg, type=Path)
    a = p.parse_args()
    source, objects, work = a.source.resolve(), a.objects.resolve(), a.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    root = work / "src"
    root.mkdir(exist_ok=False)
    view = work / "objects"
    view.mkdir(exist_ok=False)
    evidence = json.loads((source / "fused.json").read_text())
    names = (source / "external.txt").read_text().splitlines()
    if len(set(names)) != evidence["unchanged_external_modules"] or len(names) != 164451:
        raise ValueError("Unexpected external module inventory")
    if set(evidence["affected_source_modules"]).intersection(names):
        raise ValueError("A superseded native object is on the import path")
    main_file = root / "Main.lean"
    shutil.copyfile(source / "Main.lean", main_file)
    if hashlib.sha256(main_file.read_bytes()).hexdigest() != evidence["root_sha256"]:
        raise ValueError("Source does not match the distributed archive")
    for name in names:
        path = project_file(name).with_suffix(".olean")
        original = objects / path
        dest = view / path
        if not original.is_file():
            raise FileNotFoundError(original)
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.symlink_to(original)
    external = [Path(d).resolve() for d in os.environ["LEAN_PATH"].split(os.pathsep) if ".lake/packages/" in d]
    if not any((d / "Mathlib.olean").is_file() for d in external):
        raise RuntimeError("Missing Mathlib cache")
    if any((d / "Main.olean").exists() or (d / "Development").exists() for d in external):
        raise RuntimeError("Unexpected original project search path")
    env = os.environ | {"LEAN_PATH": os.pathsep.join(map(str, [view, *external]))}
    log = work / "lean.log"
    print(f"Compiling {evidence['root_sha256']} against {len(names)} authenticated unchanged objects", flush=True)
    with log.open("w") as h:
        proc=subprocess.run(["lean", *FLAGS, "-R", str(root), "-o", str(work/"Main.olean"), str(main_file)],
                            stdout=h, stderr=subprocess.STDOUT, env=env, cwd=root)
    message=log.read_text()
    print(message, flush=True)
    proc.check_returncode()
    expected={"propext", "Classical.choice", "Quot.sound"}
    if "sorryAx" in message or "declaration uses 'sorry'" in message:
        raise ValueError("The new source contains a placeholder")
    for name in TARGETS:
        hits = re.findall("'" + re.escape(name) + r"' depends on axioms:\s*\[([^]]*)\]", message)
        if len(hits)!=1 or set(q.strip() for q in hits[0].split(","))!=expected:
            raise ValueError(f"Unexpected axiom inventory: {name}")
    if not (work/"Main.olean").is_file():
        raise RuntimeError("Missing compiled root")
    result={"compiler":subprocess.check_output(["lean","--version"],text=True).strip(),
            "root_sha256":evidence["root_sha256"],"archived_source":evidence["import_only"],
            "recompiled_source_modules":evidence["affected_source_modules"],"unmodified_objects":len(names),
            "targets":list(TARGETS),"axioms":sorted(expected)}
    (work/"native.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2),flush=True)

if __name__=="__main__":
    main()
