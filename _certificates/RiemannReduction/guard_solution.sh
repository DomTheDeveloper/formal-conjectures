#!/usr/bin/env bash
# Select the shorter proof while keeping every library declaration in the official challenge.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
challenge=$(realpath "$1")
build=$(realpath "$2")
out=$(realpath -m "$3")
mkdir -p "$out"
if [[ ! -e "$out/slice" ]]; then ln -s "$build/slice" "$out/slice"; fi
python3 "$here/preserve_challenge.py" "$challenge" "$build/index" "$out/index"
{ cat "$out/index/challenge-roots.txt"; python3 "$here/roots.py" "$out/index" all; } |
    "$build/slice" mark "$out/index" "$out/all-share" share
