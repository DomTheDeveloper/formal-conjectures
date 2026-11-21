#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
workdir="$RUNNER_TEMP/rh-parts"
mkdir -p "$workdir" "$workdir/results"
cd "$workdir"
sudo apt-get update -qq
sudo apt-get install -y -qq libzstd-dev zstd
python3 "$here/test_reduce.py"
curl --fail --location --retry 4 --silent --show-error https://math.mit.edu/~drew/grh/solution.ndjson.zst -o original.zst
bash "$here/reduce.sh" original.zst build all share
# A single input download and a single search index serve this whole lane.
for ((part=$1; part<=17; part+=$2)); do
    echo "::group::Proof part $part of 17"
    bash "$here/parts.sh" original.zst build "$part" 17 check
    selection=$(printf 'part-%02d' "$part")
    cp "build/$selection/coverage.json" "results/$selection.json"
    cp "build/$selection/kernel.log" "results/$selection.log"
    echo "::endgroup::"
done
