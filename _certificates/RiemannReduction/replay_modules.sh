#!/usr/bin/env bash
# Recheck disjoint modules with Lean's own unmodified kernel in their exact import context.
set -euo pipefail
scratch=$(realpath "$1")
lane=$2
cd "$scratch"
mkdir -p RHBatches verdicts
for i in {0..16}; do
    echo "$(jq -r '.compressed_sha256' "Part$i.json")  Part$i.olean.zst" | sha256sum -c -
    zstd -dq -o "RHBatches/Part$i.olean" "Part$i.olean.zst"
    echo "$(jq -r '.sha256' "Part$i.json")  RHBatches/Part$i.olean" | sha256sum -c -
    rm "Part$i.olean.zst"
done
export LEAN_PATH="$scratch"
for ((i=lane; i<17; i+=4)); do
    name="RHBatches.Part$i"
    echo "Rechecking $name"
    /usr/bin/time -v leanchecker "$name"
    echo "Lean 4.33.1 accepted $name $(jq -r '.sha256' "Part$i.json")" | tee "verdicts/native-$i.txt"
done
