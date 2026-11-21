#!/usr/bin/env bash
# Compile the 17 human-readable chapters against the pinned published Lean source.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(realpath "$1")
out=$(realpath -m "$2")
cd "$project"
test "$(git rev-parse HEAD:src)" = b41b516b1f7baee4d83ced235ecc71fd43c97695
test "$(cat lean-toolchain)" = leanprover/lean4:v4.33.1
mapfile -t modules < <(awk '$1=="import" && $2 !~ /^RH17\./ {print "+"$2":olean"}' "$here"/RH17/S*.lean | sort -u)
lake build "${modules[@]}"
mkdir -p "$out/RH17"
for file in "$here"/RH17/S*.lean; do
    name=$(basename "$file" .lean)
    lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -j1 -R "$2" -o "$1/RH17/$3.olean" "$4"' \
        bash "$out" "$here" "$name" "$file"
done
