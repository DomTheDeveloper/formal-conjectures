#!/usr/bin/env python3
"""Count unchanged sources whose entire project import closure also matches upstream."""
from collections import defaultdict, deque
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from materialize import UPSTREAM

HEADER_DIGEST = "568c29cf9f5569aaf8fce7856f46d390910230c0e75df9050f0defeb67624e41"


def module(path):
    return path.removesuffix(".lean").replace("/", ".")


def check(repo, project, header_stream):
    listed = subprocess.check_output(["git", "-C", str(repo), "ls-tree", "-r", "-z", UPSTREAM, "src"])
    original = {}
    for item in filter(None, listed.split(b"\0")):
        meta, path = item.split(b"\t", 1)
        if path.endswith(b".lean"):
            original[module(path.decode().removeprefix("src/"))] = meta.rsplit(b" ", 1)[1]
    size = {}
    consumers = defaultdict(list)
    changed = set()
    unchanged = 0
    accumulated = hashlib.sha256()
    for row in header_stream:
        accumulated.update(row)
        path, _, imports = json.loads(row)
        name = module(path)
        data = (project / "src" / path).read_bytes()
        size[name] = data.count(b"\n")
        git_blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest().encode()
        if git_blob != original.get(name):
            changed.add(name)
            continue
        unchanged += 1
        for target, *_ in imports:
            if target in original:
                consumers[target].append(name)
    if len(size) != 163641 or sum(size.values()) != 15478802 or accumulated.hexdigest() != HEADER_DIGEST:
        raise ValueError("Source census or parsed import headers differ")
    missing = original.keys() - size.keys()
    pending = deque(changed | missing)
    while pending:
        for dependent in consumers.pop(pending.popleft(), ()):
            if dependent not in changed:
                changed.add(dependent)
                pending.append(dependent)
    reusable = sorted(size.keys() - changed)
    return {
        "upstream_commit": UPSTREAM,
        "modules": len(size),
        "modules_with_identical_source": unchanged,
        "identical_source_and_transitive_project_imports": len(reusable),
        "lines_in_that_transitively_unchanged_source": sum(size[name] for name in reusable),
        "sorted_reusable_module_names_sha256": hashlib.sha256(("\n".join(reusable) + "\n").encode()).hexdigest(),
        "native_header_stream_sha256": HEADER_DIGEST,
    }


if __name__ == "__main__":
    import sys
    options = argparse.ArgumentParser(description=__doc__)
    options.add_argument("original", type=Path)
    options.add_argument("reduced", type=Path)
    args = options.parse_args()
    print(json.dumps(check(args.original, args.reduced, sys.stdin.buffer), indent=2))
