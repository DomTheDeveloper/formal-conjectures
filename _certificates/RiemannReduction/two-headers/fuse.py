"""Consolidate all source modules affected by the two edited imports into one native Lean root."""
import argparse
import hashlib
import io
import json
import subprocess
import sys
import tarfile
from pathlib import Path
from build import HERE, trim

def root_source(repo, graph, affected):
    seen = set()
    imports, order = [], []
    def walk(name):
        if name in seen:
            return
        seen.add(name)
        if name not in affected:
            imports.append(name)
            return
        for dep in graph[name]:
            walk(dep)
        order.append(name)
    walk("Main")
    if set(order) != affected:
        raise ValueError("The Main import tree did not visit every affected module")
    body = [f"import {name}\n".encode() for name in imports]
    for name in order:
        path = "src/" + str(trim.project_file(name))
        data = subprocess.check_output(["git", "-C", str(repo), "cat-file", "blob", trim.SOURCE + ":" + path])
        lines = data.splitlines(keepends=True)
        while lines and lines[0].startswith(b"import "):
            lines.pop(0)
        source = b"".join(lines).strip(b"\n")
        if source:
            body.extend([f"\n-- {name}\nsection\n".encode(), source, b"\nend\n"])
    # These commands check all public statements against explicit types and print their actual axioms.
    audit = (HERE.parent / "reflection-imports" / "Audit.lean").read_text().split("\n\n", 1)[1]
    body.append(b"\n" + audit.encode())
    return b"".join(body), imports

def pack(input_path, output, original_root, main, kept, affected):
    content = hashlib.sha256()
    manifest = {}
    configs = set()
    with subprocess.Popen(["zstd", "-qdc", str(input_path)], stdout=subprocess.PIPE) as decoder:
        with tarfile.open(fileobj=decoder.stdout, mode="r|", bufsize=1<<20) as inp, trim.archive_output(output) as out:
            for entry in inp:
                path = entry.name
                data = inp.extractfile(entry).read()
                if path not in trim.CONFIG:
                    name = trim.module_name(path)
                    if name == "Main":
                        if data != original_root:
                            raise ValueError("Unexpected inner Main source")
                        data = main
                    elif name in affected:
                        continue
                    if name not in kept or name in manifest:
                        raise ValueError(f"Unexpected module {name}")
                    manifest[name] = (data.count(b"\n"), [x.decode() for l in data.splitlines() if l.startswith(b"import ") for x in l.split()[1:]])
                else:
                    configs.add(path)
                content.update(path.encode()+b"\0"+hashlib.sha256(data).digest())
                info = tarfile.TarInfo(path)
                info.size = len(data)
                out.addfile(info, io.BytesIO(data))
        if decoder.wait():
            raise RuntimeError("Could not read input source archive")
    if configs != trim.CONFIG or manifest.keys() != kept or trim.reachable({k:v[1] for k,v in manifest.items()}, ["Main"]) != kept:
        raise ValueError("Fused archive has missing or unreachable sources")
    if any(n in affected and n != "Main" for _, ds in manifest.values() for n in ds):
        raise ValueError("A retained file imports a former source module")
    with output.open("rb") as f:
        packed = hashlib.file_digest(f, "sha256").hexdigest()
    lines = sum(v[0] for v in manifest.values())
    return {"lines":lines,"files":len(manifest),"lines_removed":17374215-lines,"source_sha256":content.hexdigest(),"archive_sha256":packed}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    for arg in ["repo", "evidence", "output"]:
        p.add_argument(arg,type=Path)
    p.add_argument("--archives",action="store_true")
    args=p.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    graph,_=trim.read_graph(args.repo)
    for name,spec in json.loads((HERE/"plan.json").read_text())["changes"].items():
        graph[name]=spec["imports"]
    affected=set((args.evidence/"rebuild.txt").read_text().splitlines())
    kept=set((args.evidence/"retained.txt").read_text().splitlines())-affected|{"Main"}
    mainfile,imports=root_source(args.repo,graph,affected)
    (args.output/"Main.lean").write_bytes(mainfile)
    (args.output/"external.txt").write_text("".join(n+"\n" for n in sorted(kept-{"Main"})))
    if len(kept)!=164452 or len(affected)!=13:
        raise ValueError("Project inventory mismatch")
    result={"source":trim.SOURCE,"original_file_count":175187,"fused_file_count":len(kept),
            "affected_source_modules":sorted(affected),"unchanged_external_modules":len(kept)-1,
            "root_imports":len(imports),"root_lines":mainfile.count(b"\n"),"root_sha256":hashlib.sha256(mainfile).hexdigest()}
    if result["root_sha256"] != "06d4c700d45a64cb67354449b0dc38156d872000f8adf98700fdd7df2db88dc1":
        raise ValueError("Fused root diverged from the reproduced source")
    if args.archives:
        orig=subprocess.check_output(["git","-C",str(args.repo),"cat-file","blob",trim.SOURCE+":src/Main.lean"])
        for key,name in (("import_only","Riemann_Import_Cut.tar.zst"),("combined","Riemann_Combined_Source.tar.zst")):
            result[key]=pack(args.evidence/name,args.output/name,orig,mainfile,kept,affected)
            expected_trees = {'import_only': 'dd2e498b30a99b2d79f19e46507764b648a05a86d55bd9f28d34904e88e2b884', 'combined': 'b168cea4599a73d6483383da7000208d6508eaedf06d95adf7665c6ec783481a'}
            if result[key]["source_sha256"] != expected_trees[key]:
                raise ValueError(f"Source tree mismatch for {key}")
    (args.output/"fused.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))

if __name__=="__main__":
    main()
