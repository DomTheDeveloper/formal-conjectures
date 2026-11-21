#!/usr/bin/env bash
# Produce 17 disjoint source-export fragments from the authenticated solution.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
original=$(realpath "$1")
challenge=$(realpath "$2")
scratch=$(realpath -m "$3")
mkdir -p "$scratch"
cd "$scratch"
bash "$here/reduce.sh" "$original" build all share
python3 "$here/preserve_challenge.py" "$challenge" build/index guarded
{ cat guarded/challenge-roots.txt; python3 "$here/roots.py" guarded all; } |
    build/slice mark guarded whole share
python3 "$here/roots.py" guarded primitives |
    build/slice stage-plan guarded whole plan 17 2>plan.log
cat plan.log
zstd -dcq --long=31 "$original" | build/slice stage-names guarded plan
mkdir -p pipes fragments
compressors=()
for part in {0..16}; do
    fifo="pipes/stage-$part.ndjson"
    mkfifo "$fifo"
    zstd -q -T1 -3 -f -o "fragments/stage-$part.ndjson.zst" < "$fifo" &
    compressors+=($!)
done
cleanup() {
    for child in "${compressors[@]}"; do kill "$child" 2>/dev/null || true; done
}
trap cleanup EXIT
zstd -dcq --long=31 "$original" | build/slice stage-emit guarded plan pipes
for child in "${compressors[@]}"; do wait "$child"; done
trap - EXIT
python3 "$here/module_manifest.py" plan "$scratch"
