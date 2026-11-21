#!/usr/bin/env bash
# Authenticate and unpack the 17 pinned native proof modules.
set -euo pipefail
cd "$(realpath "$1")"
mkdir -p RHBatches
for i in {0..16}; do
    echo "$(jq -r '.compressed_sha256' "Part$i.json")  Part$i.olean.zst" | sha256sum -c -
    zstd -dq -o "RHBatches/Part$i.olean" "Part$i.olean.zst"
    echo "$(jq -r '.sha256' "Part$i.json")  RHBatches/Part$i.olean" | sha256sum -c -
    rm "Part$i.olean.zst"
done
