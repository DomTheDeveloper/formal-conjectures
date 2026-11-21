"""Compile the old and new foundational modules and compare their full public interfaces with Lean."""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREFIX = "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities."
ORIGINALS = {"FrechetDerivEvaluation": "0276d588c46c0054c579df7e42badc0699142bc15e5f4a217713961730a10abe",
             "FreeModuleQuotient": "e80735020f21f5af2ab712441f6e75f9b73912f48d3a982d42e54d7e70dacfbe"}
FLAGS = ["-j1", "--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
         "-DmaxSynthPendingDepth=3", "-Dpp.unicode.fun=true", "-DmaxHeartbeats=4000000"]

def run(root, out):
    root = root.resolve()
    out = out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    stage = out / "source"
    cases, rows = [], []
    for short in ORIGINALS:
        name = PREFIX + short
        rel = Path(*name.split(".")).with_suffix(".lean")
        original = root / "src" / rel
        if hashlib.sha256(original.read_bytes()).hexdigest() != ORIGINALS[short]:
            raise ValueError(f"Unexpected pinned source for {short}")
        new_source = stage / rel
        new_source.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(HERE / (short + ".lean"), new_source)
        objects = []
        for label, base in [("original", root / "src"), ("new", stage)]:
            dest = (out / label / rel).with_suffix(".olean")
            dest.parent.mkdir(parents=True, exist_ok=True)
            print(f"Compiling {label} {short}", flush=True)
            subprocess.run(["lean", *FLAGS, "-R", str(base), "-o", str(dest), str(base / rel)], check=True)
            objects.append(str(dest))
        rows.append("\t".join([name, *objects]))
        cases.append({"module": name, "original_lines": original.read_bytes().count(b"\n"),
                      "new_lines": new_source.read_bytes().count(b"\n"),
                      "new_sha256": hashlib.sha256(new_source.read_bytes()).hexdigest()})
    spec = out / "objects.tsv"
    spec.write_text("\n".join(rows) + "\n")
    verdict = out / "kernel-verdicts.jsonl"
    subprocess.run(["lean", "-j1", "-DmaxRecDepth=100000", "-DmaxHeartbeats=4000000",
                    str(HERE.parent / "refinements" / "CompareSource.lean")],
                   env=os.environ | {"RH_COMPARE_FILES": str(spec), "RH_COMPARE_OUTPUT": str(verdict)}, check=True)
    checked = [json.loads(line) for line in verdict.read_text().splitlines()]
    if len(checked) != len(cases):
        raise ValueError("Missing a comparison")
    for case, result in zip(cases, checked, strict=True):
        if case["module"] != result["module"] or result["failures"] or result["publicDeclarations"] != 1:
            raise ValueError(result)
        case["kernel"] = result
    (out / "result.json").write_text(json.dumps(cases, indent=2) + "\n")
    print(json.dumps(cases, indent=2))

if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("original", type=Path)
    p.add_argument("output", type=Path)
    a = p.parse_args()
    run(a.original, a.output)
