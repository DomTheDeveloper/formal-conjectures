#!/usr/bin/env bash
# Link the new Lean proof to the true dependency closure of the authenticated export.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
challenge=$(realpath "$1")
build=$(realpath "$2")
out=$(realpath -m "$3")
mkdir -p "$out"
if [[ ! -e "$out/slice" ]]; then ln -s "$build/slice" "$out/slice"; fi
python3 "$here/../preserve_challenge.py" "$challenge" "$build/index" "$out/index"
python3 "$here/link_tail.py" scan "$out/index" "$here/chapters.ndjson.zst" "$out/link" \
    RH17.riemannHypothesisFromPublishedArithmetic --alias riemannHypothesis
python3 "$here/choose_roots.py" roots "$out/index" "$out/link/root-ids.txt" |
    "$build/slice" mark "$out/index" "$out/ordinary-chapters" share
python3 "$here/choose_roots.py" audit "$out/index" "$out/ordinary-chapters" | tee "$out/link/closure.json"
# The authenticated 4.33.1 archive uses universe IDs from 0 to 21604.
python3 "$here/link_tail.py" tail "$out/link" "$here/chapters.ndjson.zst" "$out/ordinary-chapters" 21604 > "$out/extension.ndjson"
