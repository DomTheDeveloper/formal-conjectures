#!/usr/bin/env bash
# Encode a genuine fragment with the pinned exporter parser, then compare every
# constant read back from the native file. The stock kernel runs in a separate job.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
scratch=$(realpath "$1")
part=$2
cd "$scratch"
echo "$(jq -r ".modules[$part].fragment_sha256" module-plan.json)  stage-$part.ndjson.zst" | sha256sum -c -
mkdir -p parser
git init -q parser/exporter
git -C parser/exporter fetch -q --depth 1 https://github.com/leanprover/lean4export 15f6055e299ad5b89345e533cc2192f4cc00f659
git -C parser/exporter checkout -q --detach FETCH_HEAD
cp parser/exporter/Export/Parse.lean parser/ParseExport33.lean
cp "$here/MakeStage.lean" parser/
(
    cd parser
    lean -R . -o ParseExport33.olean -c ParseExport33.c ParseExport33.lean
    LEAN_PATH="$PWD" lean -R . -o MakeStage.olean -c MakeStage.c MakeStage.lean
    leanc -O3 -DNDEBUG -o make-stage ParseExport33.c MakeStage.c
)
prior=-
if ((part)); then prior="RHBatches.Part$((part-1))"; fi
zstd -dcq "stage-$part.ndjson.zst" |
    parser/make-stage /dev/stdin "$prior" "RHBatches.Part$part" "Part$part.olean" |
    tee serialize.log
zstd -q -T2 -6 -f -o "Part$part.olean.zst" "Part$part.olean"
python3 "$here/module_manifest.py" encode "$scratch" "$part"
