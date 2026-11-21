#!/usr/bin/env bash
# Recheck disjoint modules with Lean's own unmodified kernel in their exact import context.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
scratch=$(realpath "$1")
lane=$2
cd "$scratch"
bash "$here/unpack_modules.sh" "$scratch"
mkdir -p verdicts
export LEAN_PATH="$scratch"
for ((i=lane; i<17; i+=4)); do
    name="RHBatches.Part$i"
    echo "Rechecking $name"
    /usr/bin/time -v leanchecker "$name"
    echo "Lean 4.33.1 accepted $name $(jq -r '.sha256' "Part$i.json")" | tee "verdicts/native-$i.txt"
done
