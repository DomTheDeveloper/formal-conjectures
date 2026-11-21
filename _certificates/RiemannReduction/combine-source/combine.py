"""Apply published proof rewrites outside the dependency chain changed by the import cut."""
import argparse
import hashlib
import io
import json
import subprocess
import sys
import tarfile
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(BASE), str(BASE / "reflection-imports")]
import refine_source
import trim

EXPECTED_TREE = "4ae36c40d1c552c5f8ea189f2743356d57e23cfdeb89f7d029b56571462aa267"

def combine(repo, evidence, archive_path):
    kept = set((evidence / "retained.txt").read_text().splitlines())
    removed = set((evidence / "excluded.txt").read_text().splitlines())
    affected = (evidence / "rebuild.txt").read_text().splitlines()
    originals = {}
    for name in affected:
        path = "src/" + str(trim.project_file(name))
        originals[name] = subprocess.check_output(["git", "-C", str(repo), "cat-file", "blob", trim.SOURCE + ":" + path])
    graph = {}
    digest = hashlib.sha256()
    lines = 0
    with trim.archive_output(archive_path) as archive:
        def visit(path, data):
            nonlocal lines
            if path.startswith("src/") and path.endswith(".lean"):
                name = trim.module_name(path)
                if name not in kept:
                    return
                if name in originals:
                    data = originals[name]
                if name == trim.MODULE:
                    data = trim.rewrite(data)
                graph[name] = [word.decode() for line in data.splitlines() if line.startswith(b"import ")
                               for word in line.split()[1:]]
                lines += data.count(b"\n")
            elif path not in trim.CONFIG:
                raise ValueError(f"Unexpected source path {path}")
            digest.update(path.encode() + b"\0" + hashlib.sha256(data).digest())
            info = tarfile.TarInfo(path)
            info.size = len(data)
            archive.addfile(info, io.BytesIO(data))
        prior = refine_source.run(repo, None, visit)
    if set(graph) != kept or trim.reachable(graph, ["Main"]) != kept:
        raise ValueError("The combined tree changed the reachable module set")
    if any(removed.intersection(imports) for imports in graph.values()):
        raise ValueError("The combined tree imports a removed module")
    if (len(graph), lines, digest.hexdigest()) != (165124, 16380629, EXPECTED_TREE):
        raise ValueError("The independently measured source digest or inventory changed")
    with archive_path.open("rb") as file:
        packed = hashlib.file_digest(file, "sha256").hexdigest()
    return {"original_revision": trim.SOURCE, "source_lines": lines, "source_files": len(graph),
            "original_lines": 17374215, "lines_removed": 17374215-lines,
            "all_modules_reachable": True, "omitted_imports_still_referenced": 0,
            "source_sha256": digest.hexdigest(), "archive_sha256": packed,
            "prior_source_sha256": prior["tree_sha256"], "clean_source_rebuild": "not performed"}

if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("repo", type=Path)
    p.add_argument("evidence", type=Path, help="output of reflection-imports/trim.py for the original revision")
    p.add_argument("archive", type=Path)
    args = p.parse_args()
    print(json.dumps(combine(args.repo, args.evidence, args.archive), indent=2))
