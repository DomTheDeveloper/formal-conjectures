#!/usr/bin/env bash
# Run after reduce.sh has authenticated and indexed the original proof.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
input=$(realpath "$1")
build=$(realpath "$2")
index="$build/index"
part="$build/source-reuse"
python3 "$here/reuse_audit.py" prepare "$index" "$part"
{ cat "$part/required.txt"; python3 "$here/roots.py" "$index" primitives; } |
    "$build/slice" types "$index" "$part"
python3 "$here/dictionary.py" "$index" "$part"
zstd -dcq --long=31 "$input" | LC_ALL=C grep -aE '^\{"il":[0-9]+,"param":[0-9]+\}$' > "$part/universe-levels.ndjson"
python3 "$here/reuse_audit.py" append "$index" "$part" > "$part/new-proofs.ndjson"
{ bash "$here/emit.sh" "$input" "$build" source-reuse || exit 2; cat "$part/new-proofs.ndjson"; } |
    leanchecker --from-export /dev/stdin
