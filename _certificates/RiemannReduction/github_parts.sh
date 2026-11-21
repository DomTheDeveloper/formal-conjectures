#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
test "${GITHUB_ACTIONS:-false}" = true
workdir="$RUNNER_TEMP/rh-parts"
mkdir -p "$workdir" "$workdir/results"
cd "$workdir"
sudo apt-get update -qq
sudo apt-get install -y -qq libzstd-dev zstd
python3 "$here/test_reduce.py"
curl --fail --location --retry 4 --silent --show-error https://math.mit.edu/~drew/grh/solution.ndjson.zst -o original.zst
bash "$here/reduce.sh" original.zst build all share
# Large articles can outgrow a standard runner's physical memory.
available_mib=$(df -Pm . | awk 'END{print $4}')
swap_mib=$((available_mib-8192))
if ((swap_mib>32768)); then swap_mib=32768; fi
if ((swap_mib>=1024)); then
    if sudo fallocate -l "${swap_mib}M" replay.swap && sudo chmod 600 replay.swap &&
            sudo mkswap replay.swap && sudo swapon replay.swap; then
        free -h
    else
        sudo rm -f replay.swap
    fi
fi
for ((part=$1; part<=17; part+=$2)); do
    echo "::group::Proof part $part of 17"
    selection=$(printf 'part-%02d' "$part")
    result=0
    bash "$here/parts.sh" original.zst build "$part" 17 check || result=$?
    for item in coverage.json kernel.log restored-roots.txt; do
        if test -f "build/$selection/$item"; then
            cp "build/$selection/$item" "results/$selection-$item"
        fi
    done
    if ((result)); then exit "$result"; fi
    echo "::endgroup::"
done
