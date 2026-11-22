#!/usr/bin/env python3
"""Recreate the reduced Lean files from the author's pinned Git objects and check every byte."""
import argparse
import hashlib
import io
import json
import lzma
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import tarfile
import tempfile

HERE = Path(__file__).resolve().parent
UPSTREAM = "40e56bab026552e089d7afcfeff08d2defb9c005"
EXPECTED = (163641, 15478802, 900710896, "f24045c06732e9797163e99d6221ee9b93c130ad4aa8e463b7195a713e19dbc1")
CONFIG = ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "LICENSE-CompactRH")


def read_edits():
    pieces = sorted(HERE.glob("source-changes.xz.*"))
    if not pieces:
        raise ValueError("Missing source changes")
    records = {}
    with lzma.open(io.BytesIO(b"".join(piece.read_bytes() for piece in pieces)), "rt", encoding="utf-8") as lines:
        for line in lines:
            path, *change = json.loads(line)
            rel = PurePosixPath(path)
            if (len(change) > 1 or rel.is_absolute() or ".." in rel.parts or str(rel) != path
                    or rel.suffix != ".lean" or path in records):
                raise ValueError(f"Invalid or duplicate project path {path}")
            records[path] = change[0] if change else None
    return records


def apply_edits(data, edits, path):
    if edits is None:
        return data
    if not isinstance(edits, list):
        raise ValueError(f"New file collides with upstream file {path}")
    lines = data.splitlines(keepends=True)
    bound = len(lines)
    for start, count, *replacement in reversed(edits):
        if len(replacement) > 1 or min(start, count) < 0 or start + count > bound:
            raise ValueError(f"Invalid source edit in {path}")
        lines[start:start + count] = [value.encode("utf-8") for value in replacement]
        bound = start
    return b"".join(lines)


def reconstruct(repo, stage):
    edits = read_edits()
    hashes = {}
    source_bytes = source_lines = 0

    def accept(path, data):
        nonlocal source_bytes, source_lines
        hashes[path] = hashlib.sha256(data).digest()
        source_bytes += len(data)
        source_lines += data.count(b"\n")
        if stage is not None:
            target = stage / "src" / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)

    with subprocess.Popen(["git", "-C", str(repo), "archive", UPSTREAM, "src"], stdout=subprocess.PIPE) as proc:
        with tarfile.open(fileobj=proc.stdout, mode="r|") as archive:
            for member in archive:
                path = member.name.removeprefix("src/")
                if member.isfile() and path in edits:
                    accept(path, apply_edits(archive.extractfile(member).read(), edits[path], path))
        if proc.wait():
            raise RuntimeError(f"Could not read the upstream Git revision {UPSTREAM}")

    fingerprint = hashlib.sha256()
    for path, edit in edits.items():
        if path not in hashes:
            if not isinstance(edit, str):
                raise ValueError(f"Missing upstream file {path}")
            accept(path, edit.encode("utf-8"))
        fingerprint.update(path.encode("utf-8") + b"\0" + hashes[path])

    numbers = (len(hashes), source_lines, source_bytes, fingerprint.hexdigest())
    if numbers != EXPECTED:
        raise ValueError(f"Reconstructed source differs from the published volume: {numbers}")
    if stage is not None:
        for name in CONFIG:
            shutil.copyfile(HERE / name, stage / name)
    return dict(zip(("modules", "lean_lines", "source_bytes", "ordered_source_sha256"), numbers))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("original", type=Path, help="clone of leanprover-community/riemann-hypothesis")
    parser.add_argument("output", nargs="?", type=Path, help="new project directory; omit to verify in memory")
    args = parser.parse_args()
    if args.output is None:
        result = reconstruct(args.original, None)
    else:
        output = args.output.absolute()
        if output.exists() or output.is_symlink():
            parser.error(f"Output already exists: {output}")
        output.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=output.parent) as temp:
            stage = Path(temp) / "project"
            stage.mkdir()
            result = reconstruct(args.original, stage)
            stage.rename(output)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
