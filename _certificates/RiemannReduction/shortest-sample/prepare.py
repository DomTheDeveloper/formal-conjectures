"""Extract two closed 256-module source projects for 104 proof substitutions in the smallest archive."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/"reflection-imports"))
from trim import SOURCE, read_graph, reachable

def sha(path):
    with path.open("rb") as f: return hashlib.file_digest(f,"sha256").hexdigest()

def rel(name):
    return Path("src")/Path(*name.split(".")).with_suffix(".lean")

def header(data):
    lines=data.splitlines(keepends=True)
    return b"".join(lines[next((i for i,v in enumerate(lines) if not v.startswith(b"import ")),len(lines)):])

def main(original,archive,out):
    if sha(archive)!="afad4e86236d8400a2a5937442f24e6c00ee0df0800c735d6e80c4f94a5ca2e8":
        raise ValueError("Unexpected source archive")
    if subprocess.check_output(["git","-C",str(original),"rev-parse","HEAD"],text=True).strip()!=SOURCE:
        raise ValueError("Unexpected original commit")
    roots=json.loads((HERE/"roots.json").read_text())
    graph,_=read_graph(original)
    union=reachable(graph,roots)
    if len(roots)!=104 or len(set(roots))!=104 or len(union)!=256 or "Main" in union:
        raise ValueError("Unexpected closed source inventory")
    if any(not 1<len(reachable(graph,[n]))<=5 for n in roots):
        raise ValueError("Expected at most five project files per selected target")
    needed={str(rel(name)):name for name in union}
    configs={"lakefile.toml","lake-manifest.json","lean-toolchain"}
    before,after=(out/"original",out/"shortened")
    before.mkdir(parents=True,exist_ok=False)
    after.mkdir(parents=True,exist_ok=False)
    counts=[0,0]
    body_edits=[]
    with subprocess.Popen(["zstd","-qdc",str(archive)],stdout=subprocess.PIPE) as decomp:
        with tarfile.open(fileobj=decomp.stdout,mode="r|",bufsize=1<<20) as t:
            for item in t:
                path=item.name
                if path not in needed and path not in configs: continue
                small=t.extractfile(item).read()
                old=(original/path).read_bytes()
                if path in needed:
                    n=needed.pop(path)
                    counts[0]+=old.count(b"\n")
                    counts[1]+=small.count(b"\n")
                    if header(old)!=header(small): body_edits.append(n)
                    imports=[q.decode() for line in small.splitlines() if line.startswith(b"import ") for q in line.split()[1:]]
                    if any(d in graph and d not in union for d in imports):
                        raise ValueError(f"Unresolved project import in {n}")
                else:
                    configs.remove(path)
                    if old!=small:raise ValueError("Lake configuration changed")
                for base,data in [(before,old),(after,small)]:
                    dest=base/path
                    dest.parent.mkdir(parents=True,exist_ok=True)
                    dest.write_bytes(data)
        if decomp.wait():raise RuntimeError("Archive read failed")
    if needed or configs or set(body_edits)!=set(roots):
        raise ValueError(f"The isolated project has an unexpected set of proof changes: {set(body_edits)^set(roots)}")
    for base in (before,after):
        (base/"src/Main.lean").write_text("".join(f"import {n}\n" for n in roots))
        (base/".lake").mkdir()
        if (original/".lake/packages").exists():
            os.symlink(original/".lake/packages",base/".lake/packages",target_is_directory=True)
    manifest={"roots":roots,"project_modules":sorted(union),"original_lines":counts[0],"shortened_lines":counts[1],"changed_bodies":len(body_edits)}
    (out/"selection.json").write_text(json.dumps(manifest,indent=2)+"\n")
    print(f"{len(roots)} changed proofs files, {len(union)} project sources, {counts[0]} original and {counts[1]} revised lines",flush=True)

if __name__=="__main__":
    main(*[Path(x).resolve() for x in sys.argv[1:]])
