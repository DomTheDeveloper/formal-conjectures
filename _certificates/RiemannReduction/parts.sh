#!/usr/bin/env bash
# Emit or replay a complete declaration interval with the stock native Lean kernel.
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
parent="$scratch/all-share"
support="$scratch/computational-support"
mkdir -p "$support" "$selection"
# Reuse the global protection graph across a lane. Recompute it whenever the
# input, implementation or parent selection changes.
stamp=$(sha256sum "$index/complete" "$parent/decls.bits" | sha256sum | cut -d' ' -f1)
(
    flock 9
    if [[ ! -f "$support/complete" || "$(cat "$support/complete")" != "$stamp" ]]; then
        python3 "$here/roots.py" "$index" primitives | "$scratch/slice" protect "$index" "$parent" "$support"
        echo "$stamp" > "$support/complete"
    fi
) 9>"$support/prepare.lock"
if [[ ! -f "$selection/support-stamp" || "$(cat "$selection/support-stamp")" != "$stamp" ]]; then
    rm -f "$selection/restored-roots.txt"
    echo "$stamp" > "$selection/support-stamp"
fi
while true; do
    protected="$support"
    if [[ -s "$selection/restored-roots.txt" ]]; then
        protected="$selection/extra-support"
        while IFS= read -r root; do
            python3 "$here/roots.py" "$index" "$root"
        done < "$selection/restored-roots.txt" | "$scratch/slice" protect "$index" "$parent" "$protected"
    fi
    python3 "$here/roots.py" "$index" primitives |
        "$scratch/slice" shard "$index" "$parent" "$selection" "$((part_number-1))" "$parts" "$protected"
    python3 "$here/dictionary.py" "$index" "$selection"
    python3 "$here/audit_part.py" "$index" "$parent" "$selection" | tee "$selection/coverage.json"
    case "$action" in
        emit)
            bash "$here/emit.sh" "$input" "$scratch" "$part" | zstd -T1 -5 -f -o "$scratch/$part.ndjson.zst"
            break ;;
        check)
            set +e
            bash "$here/emit.sh" "$input" "$scratch" "$part" |
                leanchecker --from-export /dev/stdin 2>&1 | tee "$selection/kernel.log"
            status=("${PIPESTATUS[@]}")
            set -e
            if ((status[0]==0 && status[1]==0 && status[2]==0)) &&
                grep -Fq 'Lean default kernel accepts the solution' "$selection/kernel.log"; then
                break
            fi
            reason=$(sed -n "s/.*while replaying declaration '\(.*\)':$/\1/p" "$selection/kernel.log" | head -1)
            if [[ -z "$reason" ]] || grep -Fxq -- "$reason" "$selection/restored-roots.txt" 2>/dev/null; then
                echo "Kernel replay failed (emitter=${status[0]}, kernel=${status[1]}, log=${status[2]})." >&2
                exit 1
            fi
            echo "Restoring all proof bodies reachable from $reason before retrying." >&2
            printf '%s\n' "$reason" >> "$selection/restored-roots.txt" ;;
        *) exit 2 ;;
    esac
done
