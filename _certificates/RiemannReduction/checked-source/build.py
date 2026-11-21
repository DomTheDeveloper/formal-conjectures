"""Build the source project whose changed proof bodies have individual native comparisons."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path[:0] = [str(BASE), str(BASE / "reflection-imports"), str(BASE / "longest-source")]
from refine_source import read_refinements, rewrite
from shorten import NAME as LONGEST, simplify
from trim import SOURCE, archive_output

INPUT = "cdc7d1c4439e1930ffbdea694614520215502cafef549800b56b3bf12f65dd4c"
ROOT = "06d4c700d45a64cb67354449b0dc38156d872000f8adf98700fdd7df2db88dc1"
LONGEST_SHA = "ae6c20cdfefcb91c08cfc129f39ba68b7059b539cc2bf197cbe5ba396949b76b"
SHORT = "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities."
SHORT_FILES = {SHORT + n: BASE / "short-proofs" / (n + ".lean") for n in ("FreeModuleQuotient", "FrechetDerivEvaluation")}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def file_sha(path):
    with path.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()

def source_parts(data):
    lines = data.splitlines(keepends=True)
    boundary = next((i for i, line in enumerate(lines) if not line.startswith(b"import ")), len(lines))
    imports = [s.decode() for line in lines[:boundary] for s in line.split()[1:]]
    return imports, b"".join(lines[boundary:])

def build(archive, original, output):
    if file_sha(archive) != INPUT:
        raise ValueError("Unexpected input source archive")
    if subprocess.check_output(["git", "-C", str(original), "rev-parse", "HEAD"], text=True).strip() != SOURCE:
        raise ValueError("Unexpected upstream revision")
    refinements = {item["module"]:item for item in read_refinements()}
    changed = set(refinements) | set(SHORT_FILES) | {LONGEST}
    if len(changed) != 34:
        raise ValueError("Expected 33 Mathlib-only files and one project-dependent file")
    output.mkdir(parents=True, exist_ok=True)
    output_archive = output / "Riemann_Compared_Source.tar.zst"
    digest = hashlib.sha256()
    graph, paired = {}, {}
    lines = 0
    restored = []
    with subprocess.Popen(["zstd", "-qdc", str(archive)], stdout=subprocess.PIPE) as decoder:
        with tarfile.open(fileobj=decoder.stdout, mode="r|", bufsize=1<<20) as source, archive_output(output_archive) as target:
            for entry in source:
                data = source.extractfile(entry).read()
                if entry.name.startswith("src/") and entry.name.endswith(".lean"):
                    name = entry.name[4:-5].replace("/", ".")
                    if name in graph:
                        raise ValueError(f"Duplicate file {name}")
                    if name in changed:
                        old = (original / entry.name).read_bytes()
                        if name == LONGEST:
                            old_header, old_body = source_parts(old)
                            base_header, base_body = source_parts(data)
                            if base_body != old_body or set(base_header) - set(old_header):
                                raise ValueError("The original longest-file proof body changed")
                            restored = sorted(set(old_header) - set(base_header))
                            new = simplify(old)
                            if sha(new) != LONGEST_SHA or len(restored) != 11:
                                raise ValueError("Unexpected longest-file rewrite")
                        else:
                            if old != data or source_parts(old)[0] != ["Mathlib"]:
                                raise ValueError(f"Expected original Mathlib-only module {name}")
                            new = SHORT_FILES[name].read_bytes() if name in SHORT_FILES else rewrite(old, refinements[name])
                            if source_parts(new)[0] != ["Mathlib"]:
                                raise ValueError(f"Unexpected import in {name}")
                        paired[name] = {"original_sha256":sha(old), "revised_sha256":sha(new),
                                        "source_before":old.count(b"\n"), "source_after":new.count(b"\n")}
                        data = new
                    if name == "Main" and sha(data) != ROOT:
                        raise ValueError("Consolidated root changed")
                    graph[name] = [s.decode() for line in data.splitlines() if line.startswith(b"import ") for s in line.split()[1:]]
                    lines += data.count(b"\n")
                digest.update(entry.name.encode() + b"\0" + hashlib.sha256(data).digest())
                meta = tarfile.TarInfo(entry.name)
                meta.size = len(data)
                target.addfile(meta, io.BytesIO(data))
        if decoder.wait():
            raise RuntimeError("Could not decompress the original archive")
    visited, pending = set(), ["Main"]
    while pending:
        n = pending.pop()
        if n in graph and n not in visited:
            visited.add(n)
            pending.extend(graph[n])
    if changed != set(paired) or visited != set(graph) or set(restored)-visited:
        raise ValueError("The archive omits a changed or dependent module")
    if (len(visited),lines) != (164452,16337345):
        raise ValueError(f"Unexpected archive measurements: {len(visited)} and {lines}")
    receipt = {"upstream_commit":SOURCE,"input_archive_sha256":INPUT,"source_sha256":digest.hexdigest(),
               "archive_sha256":file_sha(output_archive),"modules":len(visited),"physical_lean_lines":lines,
               "lines_removed":17374215-lines,"root_source_sha256":ROOT,"reinstated_original_imports_in_longest":restored,
               "mathlib_only":sorted(changed-{LONGEST}),"longest":LONGEST,"individual_files":paired}
    (output / "source.json").write_text(json.dumps(receipt,sort_keys=True,indent=2) + "\n")
    print(json.dumps({k:receipt[k] for k in ("modules","physical_lean_lines","lines_removed","source_sha256","archive_sha256")}))

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for param in ("input_archive","original","output"):
        parser.add_argument(param,type=Path)
    a = parser.parse_args()
    build(a.input_archive,a.original,a.output)
