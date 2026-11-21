"""Generate and audit two source trees after removing unnecessary imports at two proof steps."""
import argparse
import hashlib
import io
import json
import subprocess
import sys
import tarfile
from graphlib import TopologicalSorter
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE.parent), str(HERE.parent / "reflection-imports")]
import trim
import refine_source

def rewrite(name, data, changes):
    spec = changes[name]
    if hashlib.sha256(data).hexdigest() != spec["source_sha256"]:
        raise ValueError(f"Original module changed: {name}")
    header, delimiter, body = data.partition(b"\n\n")
    if not delimiter or len(header.splitlines()) != spec["original_imports"] or not all(l.startswith(b"import ") for l in header.splitlines()):
        raise ValueError(f"Unexpected header for {name}")
    return b"\n".join(b"import " + d.encode() for d in spec["imports"]) + delimiter + body

def main():
    p = argparse.ArgumentParser(description=__doc__)
    for arg in ["repo", "inventory", "out"]:
        p.add_argument(arg, type=Path)
    p.add_argument("--source", type=Path, help="Extract the import-only tree for a native rebuild")
    p.add_argument("--archives", action="store_true", help="Package both the import-only and combined source")
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    if args.source:
        args.source.mkdir(parents=True, exist_ok=False)
    plan = json.loads((HERE / "plan.json").read_text())
    changes = plan["changes"]
    graph, original_sizes = trim.read_graph(args.repo)
    for name, spec in changes.items():
        graph[name] = spec["imports"]
    kept = trim.reachable(graph, ["Main"])
    omitted = graph.keys() - kept
    rev = {n: [] for n in kept}
    for n in kept:
        for d in graph[n]:
            if d in kept: rev[d].append(n)
    downstream = trim.reachable(rev, changes)
    order = list(TopologicalSorter({n: [d for d in graph[n] if d in downstream] for n in sorted(downstream)}).static_order())
    omitted_lines = sum(original_sizes[n] for n in omitted)
    if (len(omitted), omitted_lines, len(downstream)) != (10723, 785588, 13):
        raise ValueError("Dependency closure differs from the measured edit")
    audited = trim.audit_constants(args.inventory, graph, omitted)
    for filename, names in (("rebuild.txt", order), ("retained.txt", sorted(kept)), ("excluded.txt", sorted(omitted))):
        (args.out / filename).write_text("".join(n + "\n" for n in names))

    originals = {}
    for name in downstream:
        path = "src/" + str(trim.project_file(name))
        originals[name] = subprocess.check_output(["git", "-C", str(args.repo), "cat-file", "blob", trim.SOURCE + ":" + path])
    for variant in (["source", "combined"] if args.archives else ["source"]):
        tar_path = args.out / ("Riemann_Import_Cut.tar.zst" if variant == "source" else "Riemann_Combined_Source.tar.zst")
        digest = hashlib.sha256()
        lines = 0
        imports = {}
        with trim.archive_output(tar_path if args.archives else None) as archive:
            def add_file(path, data):
                nonlocal lines
                if path not in trim.CONFIG:
                    name = trim.module_name(path)
                    if name not in kept: return
                    if name in originals:
                        data = originals[name]
                    if name in changes:
                        data = rewrite(name, data, changes)
                    lines += data.count(b"\n")
                    imports[name] = [d.decode() for line in data.splitlines() if line.startswith(b"import ") for d in line.split()[1:]]
                digest.update(path.encode() + b"\0" + hashlib.sha256(data).digest())
                if args.source and variant == "source":
                    dest = args.source / path
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    dest.write_bytes(data)
                if archive is not None:
                    info = tarfile.TarInfo(path)
                    info.size = len(data)
                    archive.addfile(info, io.BytesIO(data))
            if variant == "source":
                for path, data in trim.sources(args.repo):
                    add_file(path, data)
            else:
                prior = refine_source.run(args.repo, None, add_file)
        if set(imports) != kept or trim.reachable(imports, ["Main"]) != kept or any(omitted.intersection(ds) for ds in imports.values()):
            raise ValueError("Delivered source does not match the reachable import tree")
        if variant == "source" and lines != 16588344:
            raise ValueError("Unexpected import-only source size")
        report = {"original_revision": trim.SOURCE, "original_files": len(graph), "original_lines": sum(original_sizes.values()),
                  "variant": variant, "remaining_modules": len(kept), "remaining_lines": lines,
                  "lines_removed": sum(original_sizes.values())-lines, "omitted_modules": len(omitted),
                  "omitted_module_lines": omitted_lines, "header_edits": list(changes), "affected_modules": order,
                  "all_reachable_from_Main": True, "omitted_imports_still_referenced": 0,
                  "kernel_export_audit": audited, "content_sha256": digest.hexdigest()}
        if variant == "combined":
            report["prior_tree_sha256"] = prior["tree_sha256"]
        if args.archives:
            with tar_path.open("rb") as f:
                report["archive_sha256"] = hashlib.file_digest(f, "sha256").hexdigest()
        (args.out / (variant + ".json")).write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({k:v for k,v in report.items() if k not in {"affected_modules","header_edits"}}, indent=2),flush=True)

if __name__ == "__main__":
    main()
