"""Build the source project reachable from Main after trimming the reflection module's imports."""
import argparse
import csv
import gzip
import hashlib
import io
import json
import subprocess
import sys
import tarfile
from contextlib import contextmanager
from graphlib import TopologicalSorter
from pathlib import Path

SOURCE = "40e56bab026552e089d7afcfeff08d2defb9c005"
TREE = "b41b516b1f7baee4d83ced235ecc71fd43c97695"
MODULE = "Development.AutomorphicArithmetic.CharacterBoxes.RiemannHypothesisOfEveryCharacter"
IMPORTS = (
    "Mathlib",
    "Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineOneParameterHomomorphism",
    "Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter",
)
ORIGINAL_FILE = "80d57d0936668a1cde784b87c67f680d017962b6cecf0710a51a32b9d8549880"
CONSTANTS = "28e2367d1a48ef51f82bf6e42fe1bddbc12f9778bf62846168b1b06ec75947c5"
CONFIG = {"lean-toolchain", "lakefile.toml", "lake-manifest.json"}


def module_name(path):
    return path.removeprefix("src/").removesuffix(".lean").replace("/", ".")


def project_file(name):
    return Path(*name.split(".")).with_suffix(".lean")


def rewrite(data):
    if hashlib.sha256(data).hexdigest() != ORIGINAL_FILE:
        raise ValueError("The original reflection module does not match the pinned source")
    header, blank, body = data.partition(b"\n\n")
    if not blank or len(header.splitlines()) != 209 or not all(s.startswith(b"import ") for s in header.splitlines()):
        raise ValueError("Unexpected original import header")
    return "\n".join(f"import {name}" for name in IMPORTS).encode() + blank + body


def sources(repo):
    with subprocess.Popen(["git", "-C", str(repo), "archive", SOURCE], stdout=subprocess.PIPE) as process:
        with tarfile.open(fileobj=process.stdout, mode="r|", bufsize=1024 * 1024) as archive:
            for file in archive:
                if file.isfile() and (file.name in CONFIG or file.name.startswith("src/") and file.name.endswith(".lean")):
                    yield file.name, archive.extractfile(file).read()
        if process.wait() != 0:
            raise RuntimeError("Cannot read the pinned Git archive")


def reachable(graph, start):
    seen = set()
    todo = list(start)
    while todo:
        name = todo.pop()
        if name in graph and name not in seen:
            seen.add(name)
            todo.extend(graph[name])
    return seen


def read_graph(repo):
    root = subprocess.check_output(["git", "-C", str(repo), "rev-parse", SOURCE + ":src"], text=True).strip()
    if root != TREE:
        raise ValueError("Published Lean source tree mismatch")
    graph, lines = {}, {}
    for path, data in sources(repo):
        if path in CONFIG:
            continue
        module = module_name(path)
        lines[module] = data.count(b"\n")
        imports = []
        for line in data.splitlines():
            if line.startswith(b"import "):
                imports.extend(line.removeprefix(b"import ").decode().split())
        graph[module] = imports
    if (len(graph), sum(lines.values())) != (175187, 17374215) or len(reachable(graph, ["Main"])) != len(graph):
        raise ValueError("Published project inventory mismatch")
    return graph, lines


def audit_constants(path, graph, excluded):
    with path.open("rb") as f:
        if hashlib.file_digest(f, "sha256").hexdigest() != CONSTANTS:
            raise ValueError("Unexpected published kernel-constant inventory")
    total = checked = 0
    with gzip.open(path, "rt", newline="") as handle:
        for row in csv.DictReader(handle):
            total += 1
            if row["origin"] == "project" and row["in_export"] == "true":
                if row["module"] not in graph or row["module"] in excluded:
                    raise ValueError(f'Export needs {row["name"]} from {row["module"]}')
                checked += 1
    if total != 1484733 or not checked:
        raise ValueError("Incomplete inventory")
    return {"inventory_constants": total, "project_constants_in_export": checked, "from_excluded_modules": 0}


@contextmanager
def archive_output(path):
    if path is None:
        yield None
        return
    try:
        with path.open("xb") as file:
            with subprocess.Popen(["zstd", "-q", "-6", "-T2", "-c"], stdin=subprocess.PIPE, stdout=file) as encoder:
                with tarfile.open(fileobj=encoder.stdin, mode="w|", bufsize=1024 * 1024) as archive:
                    yield archive
                encoder.stdin.close()
                if encoder.wait() != 0:
                    raise RuntimeError("Source compression failed")
    except FileExistsError:
        raise
    except BaseException:
        path.unlink(missing_ok=True)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("evidence", type=Path)
    parser.add_argument("--source", type=Path, help="create an extracted source project at a new path")
    parser.add_argument("--archive", type=Path, help="create a complete .tar.zst at a new path")
    parser.add_argument("--constants", type=Path, help="audit every constant in the published export against the cut")
    args = parser.parse_args()
    graph, sizes = read_graph(args.repo)
    graph[MODULE] = list(IMPORTS)
    kept = reachable(graph, ["Main"])
    excluded = set(graph) - kept
    reverse = {name: [] for name in kept}
    for owner in kept:
        for imp in graph[owner]:
            if imp in kept:
                reverse[imp].append(owner)
    affected = reachable(reverse, [MODULE])
    order = list(TopologicalSorter({n: [x for x in graph[n] if x in affected] for n in sorted(affected)}).static_order())
    removed_lines = sum(sizes[n] for n in excluded)
    if (len(excluded), removed_lines, len(affected)) != (10063, 728186, 11):
        raise ValueError("Import closure differs from the measured cut")

    report = {"source": SOURCE, "published_source_tree": TREE, "edited_module": MODULE,
              "original_modules": len(graph), "original_lines": sum(sizes.values()),
              "remaining_modules": len(kept), "excluded_modules": len(excluded),
              "excluded_module_lines": removed_lines, "imports_before": 209,
              "imports_after": len(IMPORTS), "affected_in_build_order": order}
    if args.constants:
        report["kernel_export_audit"] = audit_constants(args.constants, graph, excluded)
    if args.source:
        args.source.mkdir(parents=True, exist_ok=False)
    args.evidence.mkdir(parents=True, exist_ok=True)
    totals = files = changed = 0
    digest = hashlib.sha256()
    with archive_output(args.archive) as archive:
        for path, data in sources(args.repo):
            if path not in CONFIG:
                name = module_name(path)
                if name not in kept:
                    continue
                if name == MODULE:
                    data = rewrite(data)
                    changed += 1
                totals += data.count(b"\n")
                files += 1
            digest.update(path.encode() + b"\x00" + hashlib.sha256(data).digest())
            if args.source:
                target = args.source / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
            if archive is not None:
                member = tarfile.TarInfo(path)
                member.size = len(data)
                member.mode = 0o644
                archive.addfile(member, io.BytesIO(data))
    if (files, totals, changed) != (165124, 16645823, 1):
        raise ValueError("Output file/line totals differ from the measured result")
    report.update(remaining_lines=totals, lines_removed=sum(sizes.values())-totals, changed_source_files=changed,
                  content_digest_sha256=digest.hexdigest())
    for filename, names in (("retained.txt", sorted(kept)), ("excluded.txt", sorted(excluded)), ("rebuild.txt", order)):
        (args.evidence / filename).write_text("".join(n+"\n" for n in names))
    result = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    (args.evidence / "source.json").write_text(result)
    print(result, end="")


if __name__ == "__main__":
    main()
