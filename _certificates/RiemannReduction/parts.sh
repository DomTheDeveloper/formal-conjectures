#!/usr/bin/env bash
# Emit or replay nonoverlapping proof intervals using the stock native Lean kernel.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
input=$(realpath "$1")
scratch=$(realpath "$2")
part_number=$3
parts=${4:-17}
action=${5:-check}
if (( part_number < 1 || part_number > parts )); then exit 2; fi
part=$(printf 'part-%02d' "$part_number")
index="$scratch/index"
selection="$scratch/$part"
python3 "$here/roots.py" "$index" primitives |
    "$scratch/slice" shard "$index" "$scratch/all-share" "$selection" "$((part_number-1))" "$parts"
python3 "$here/dictionary.py" "$index" "$selection"
python3 "$here/audit_part.py" "$index" "$scratch/all-share" "$selection" | tee "$selection/coverage.json"
case "$action" in
    emit)
        bash "$here/emit.sh" "$input" "$scratch" "$part" | zstd -T1 -5 -f -o "$scratch/$part.ndjson.zst" ;;
    check)
        # A pipe keeps the expanded article off disk. The negative control verifies that
        # this particular leanchecker build reads /dev/stdin and reports invalid proofs.
        bash "$here/emit.sh" "$input" "$scratch" "$part" |
            leanchecker --from-export /dev/stdin | tee "$selection/kernel.log"
        grep -Fq 'Lean default kernel accepts the solution' "$selection/kernel.log"
        ;;
    *) exit 2 ;;
esac
