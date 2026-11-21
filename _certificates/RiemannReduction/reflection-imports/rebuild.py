"""Rebuild every retained module that previously imported the changed header, and all five targets."""
import argparse
import json
import os
import re
import subprocess
from pathlib import Path
from trim import project_file

HERE = Path(__file__).resolve().parent
FLAGS = ["-j1", "--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
         "-DmaxSynthPendingDepth=3", "-DmaxHeartbeats=4000000", "-Dpp.unicode.fun=true"]
TARGETS = ("riemannHypothesis", "riemannZeta_eq_zero_re", "LFunction_ne_zero_of_half_lt_re",
           "LFunction_eq_zero_re", "LFunction_eq_zero_re_of_isPrimitive")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("project", "evidence", "published_objects", "object_view"):
        p.add_argument(name, type=Path)
    args = p.parse_args()
    root = args.project.resolve() / "src"
    evidence = args.evidence.resolve()
    view = args.object_view.resolve()
    pinned = args.published_objects.resolve()
    retained = set((evidence / "retained.txt").read_text().splitlines())
    affected = (evidence / "rebuild.txt").read_text().splitlines()
    view.mkdir(parents=True, exist_ok=False)
    for name in sorted(retained - set(affected)):
        path = project_file(name).with_suffix(".olean")
        target = pinned / path
        if not target.is_file():
            raise FileNotFoundError(target)
        link = view / path
        link.parent.mkdir(parents=True, exist_ok=True)
        link.symlink_to(target)
    # Only external Lake packages and the pinned Lean standard library are on the fallback path.
    external = [d for d in os.environ["LEAN_PATH"].split(os.pathsep)
                if ".lake/packages/" in d or "/lib/lean" in d and ("/.elan/" in d or "/toolchain/" in d)]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(view), *external]))
    if not any("/mathlib/" in d for d in external):
        raise RuntimeError("Pinned Mathlib objects not found on LEAN_PATH")
    if any((Path(d) / "Main.olean").exists() or (Path(d) / "Development").exists() for d in external):
        raise RuntimeError("An external directory also exposes published project objects")
    print(f"Using {len(retained)-len(affected)} authenticated original objects. Rebuilding {len(affected)}.", flush=True)
    for name in affected:
        rel = project_file(name)
        out = (view / rel).with_suffix(".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        if out.exists() or out.is_symlink():
            raise RuntimeError(f"Refusing to reuse an affected object: {name}")
        print(f"Compiling {name}", flush=True)
        subprocess.run(["lean", *FLAGS, "-R", str(root), "-o", str(out), str(root / rel)],
                       check=True, env=env, cwd=root)
        if not out.is_file():
            raise RuntimeError(f"No object for {name}")
        with (evidence / "recompiled.txt").open("a") as h:
            print(name, file=h)
    print("Checking all five original theorem types and axiom inventories", flush=True)
    with (evidence / "axioms.log").open("w") as log:
        result = subprocess.run(["lean", *FLAGS, str(HERE / "Audit.lean")], env=env, stdout=log,
                                stderr=subprocess.STDOUT, cwd=root)
    text = (evidence / "axioms.log").read_text()
    print(text, flush=True)
    result.check_returncode()
    expected = {"propext", "Classical.choice", "Quot.sound"}
    for name in TARGETS:
        hits = re.findall("'" + re.escape(name) + r"' depends on axioms:\s*\[([^]]*)\]", text)
        if len(hits) != 1 or {item.strip() for item in hits[0].split(",")} != expected:
            raise RuntimeError(f"Unexpected axiom inventory for {name}")
    result = {"source": json.loads((evidence / "source.json").read_text()),
              "unchanged_objects_reused": len(retained) - len(affected),
              "freshly_recompiled": affected, "theorems": list(TARGETS), "axioms": sorted(expected)}
    (evidence / "lean-verdict.json").write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: all affected source modules rebuilt, and all five unconditional theorem types and axiom inventories matched.")


if __name__ == "__main__":
    main()
