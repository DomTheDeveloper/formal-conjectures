"""Reopen the distributed archive and compare each of its 33 revised Mathlib-only files with the original."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
FLAGS = ["-j1", "--tstack=400000", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
         "-DmaxSynthPendingDepth=3", "-Dpp.unicode.fun=true", "-DmaxHeartbeats=4000000"]

def rel(name):
    return Path(*name.split(".")).with_suffix(".lean")

def extract(archive, receipt, out):
    data = json.loads(receipt.read_text())
    with archive.open("rb") as f:
        if hashlib.file_digest(f, "sha256").hexdigest() != data["archive_sha256"]:
            raise ValueError("The archive differs from the measured download")
    wanted = {"src/" + str(rel(name)):name for name in data["mathlib_only"]}
    out.mkdir(parents=True,exist_ok=False)
    with subprocess.Popen(["zstd","-qdc",str(archive)], stdout=subprocess.PIPE) as decoder:
        with tarfile.open(fileobj=decoder.stdout,mode="r|",bufsize=1<<20) as source:
            for entry in source:
                if entry.name in wanted:
                    name = wanted.pop(entry.name)
                    body = source.extractfile(entry).read()
                    if hashlib.sha256(body).hexdigest() != data["individual_files"][name]["revised_sha256"]:
                        raise ValueError(f"Archive has an unexpected source for {name}")
                    dest = out / "src" / rel(name)
                    dest.parent.mkdir(parents=True,exist_ok=True)
                    dest.write_bytes(body)
        if decoder.wait(): raise RuntimeError("Archive could not be reopened")
    if wanted: raise ValueError(f"Missing sources {list(wanted)}")
    (out / "source.json").write_bytes(receipt.read_bytes())

def compare(original, bundle, out, lane):
    data = json.loads((bundle / "source.json").read_text())
    selected = data["mathlib_only"][lane::3]
    if len(selected)!=11: raise ValueError("Expected eleven file pairs")
    out.mkdir(parents=True, exist_ok=False)
    rows = []
    for name in selected:
        objects = []
        for label, root, key in [("old",original / "src","original_sha256"), ("new",bundle / "src","revised_sha256")]:
            file = root / rel(name)
            if hashlib.sha256(file.read_bytes()).hexdigest()!=data["individual_files"][name][key]:
                raise ValueError(f"Wrong {label} bytes for {name}")
            dest = (out / label / rel(name)).with_suffix(".olean")
            dest.parent.mkdir(parents=True,exist_ok=True)
            print(f"Compiling {label} {name}",flush=True)
            subprocess.run(["lean",*FLAGS,"-R",str(root),"-o",str(dest),str(file)],check=True)
            objects.append(str(dest))
        rows.append("\t".join([name,*objects]))
    spec = out / "objects.tsv"
    spec.write_text("\n".join(rows)+"\n")
    verdict = out / "kernel-verdicts.jsonl"
    subprocess.run(["lean","-j1","-DmaxRecDepth=100000","-DmaxHeartbeats=4000000",
                    str(HERE.parent / "refinements" / "CompareSource.lean")],check=True,
                   env=os.environ|{"RH_COMPARE_FILES":str(spec),"RH_COMPARE_OUTPUT":str(verdict)})
    results = [json.loads(row) for row in verdict.read_text().splitlines()]
    if [r["module"] for r in results]!=selected or any(r["failures"] or r["publicDeclarations"]==0 for r in results):
        raise ValueError("Incomplete kernel comparison or interface mismatch")
    (out / f"lane-{lane}.json").write_text(json.dumps(results,indent=2)+"\n")

def combine(receipt, lanes, output):
    metadata = json.loads(receipt.read_text())
    rows = [r for lane in range(3) for r in json.loads((lanes / f"lane-{lane}.json").read_text())]
    if sorted(r["module"] for r in rows)!=metadata["mathlib_only"] or any(r["failures"] for r in rows):
        raise ValueError("Incomplete native verification")
    result = {"archive_sha256":metadata["archive_sha256"],"source_files":len(rows),
              "public_declarations":sum(r["publicDeclarations"] for r in rows),
              "public_definitions":sum(r["definitions"] for r in rows),"individual":rows}
    if (result["source_files"],result["public_declarations"],result["public_definitions"])!=(33,345,186):
        raise ValueError("Unexpected kernel comparison totals")
    output.write_text(json.dumps(result,indent=2)+"\n")
    print(f'All {len(rows)} pairs passed for {result["public_declarations"]} public declarations and {result["public_definitions"]} definition bodies.')

if __name__=="__main__":
    p = argparse.ArgumentParser(description=__doc__)
    modes = p.add_subparsers(dest="mode",required=True)
    e = modes.add_parser("extract")
    for label in ("archive","receipt","out"): e.add_argument(label,type=Path)
    c = modes.add_parser("compare")
    for label in ("original","bundle","out"): c.add_argument(label,type=Path)
    c.add_argument("lane",type=int,choices=range(3))
    s = modes.add_parser("combine")
    for label in ("receipt","lanes","output"): s.add_argument(label,type=Path)
    args = vars(p.parse_args())
    mode = args.pop("mode")
    {"extract":extract,"compare":compare,"combine":combine}[mode](**args)
