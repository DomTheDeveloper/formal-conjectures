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
bash "$here/guard_solution.sh" "$challenge" build protected
python3 "$here/roots.py" protected/index primitives |
    build/slice stage-plan protected/index protected/all-share plan 17 2>plan.log
cat plan.log
zstd -dcq --long=31 "$original" | build/slice stage-names protected/index plan
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
zstd -dcq --long=31 "$original" | build/slice stage-emit protected/index plan pipes
for child in "${compressors[@]}"; do wait "$child"; done
trap - EXIT
python3 "$here/module_manifest.py" plan "$scratch"
