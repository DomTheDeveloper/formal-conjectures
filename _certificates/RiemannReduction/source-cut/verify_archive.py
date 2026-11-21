"""Verify every member of the distributed proof archive against its original Git object."""
import argparse
import hashlib
import json
import subprocess
import tarfile
from pathlib import Path

REVISION = "40e56bab026552e089d7afcfeff08d2defb9c005"
CONFIG = {"lake-manifest.json", "lakefile.toml", "lean-toolchain"}
EDIT = "src/Development/AutomorphicArithmetic/CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean"
HEADER = b"""import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineOneParameterHomomorphism
import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter"""

def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])

def module(path):
    return path[4:-5].replace("/", ".")

def blob_digest(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()

def verify(repo, path):
    git_files = {}
    for entry in git(repo, "ls-tree", "-rz", REVISION).split(b"\0"):
        if not entry:
            continue
        meta, filename = entry.split(b"\t", 1)
        mode, kind, digest = meta.split()
        if kind != b"blob" or mode != b"100644":
            raise ValueError(f"Unexpected upstream object: {filename!r}")
        git_files[filename.decode()] = digest.decode()
    original = git(repo, "cat-file", "blob", git_files[EDIT])
    original_header, delimiter, original_body = original.partition(b"\n\n")
    if not delimiter or len(original_header.splitlines()) != 209:
        raise ValueError("Original header differs from the measured revision")
    originals = {module(name) for name in git_files if name.startswith("src/") and name.endswith(".lean")}
    graph, seen = {}, set()
    lines = identical = 0
    with subprocess.Popen(["zstd", "-q", "-dc", str(path)], stdout=subprocess.PIPE) as proc:
        with tarfile.open(fileobj=proc.stdout, mode="r|", bufsize=1024*1024) as tar:
            for member in tar:
                name = member.name
                if name in seen or name not in git_files or not member.isreg():
                    raise ValueError(f"Unexpected archive member: {name}")
                seen.add(name)
                data = tar.extractfile(member).read()
                if name == EDIT:
                    if data != HEADER + delimiter + original_body:
                        raise ValueError("An edit outside the expected import header was detected")
                elif blob_digest(data) != git_files[name]:
                    raise ValueError(f"Git blob mismatch: {name}")
                else:
                    identical += 1
                if name in CONFIG:
                    continue
                if not (name.startswith("src/") and name.endswith(".lean")):
                    raise ValueError(f"Unexpected file: {name}")
                imports = [word.decode() for line in data.splitlines() if line.startswith(b"import ")
                           for word in line.split()[1:]]
                graph[module(name)] = [word for word in imports if word in originals]
                lines += data.count(b"\n")
        if proc.wait() != 0:
            raise RuntimeError("Decompression failed")
    if not CONFIG.issubset(seen) or EDIT not in seen:
        raise ValueError("Missing project files")
    reachable, todo = set(), ["Main"]
    while todo:
        name = todo.pop()
        if name not in reachable:
            reachable.add(name)
            todo.extend(graph[name])
    if reachable != graph.keys() or (len(graph), lines, identical) != (165124, 16645823, 165126):
        raise ValueError("Delivered tree does not match the source closure of Main")
    with path.open("rb") as f:
        digest = hashlib.file_digest(f, "sha256").hexdigest()
    return {"original_revision": REVISION, "lean_modules": len(graph), "lean_lines": lines,
            "identical_lean_blobs": identical-len(CONFIG), "identical_project_config_blobs": len(CONFIG),
            "only_edit": EDIT, "proof_bodies_preserved": True, "all_archived_modules_reachable_from_Main": True,
            "omitted_original_modules": len(originals)-len(graph), "archive_sha256": digest}

if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("repo", type=Path)
    p.add_argument("tar_zst", type=Path)
    args = p.parse_args()
    print(json.dumps(verify(args.repo, args.tar_zst), indent=2))
