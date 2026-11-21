#!/usr/bin/env bash
# Build or reuse the search index, then select a dependency-closed proof.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
input=$(realpath "$1")
scratch=$(realpath -m "$2")
target=${3:-all}
mode=${4:-share}
mkdir -p "$scratch/index"
cd "$scratch"
expected=61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381
printf '%s  %s\n' "$expected" "$input" | sha256sum -c -
g++ -std=c++20 -O3 -DNDEBUG -Wall -Wextra -Werror "$here/slice.cpp" -lzstd -o slice
# Index files may be reused only for this fixed input and this exact reader.
stamp=$(cat "$here/catalog.py" "$here/slice.cpp" "$here/intern.hpp" "$here/stages.hpp" "$here/dictionary.py" | sha256sum | cut -d' ' -f1)
if [[ ! -f index/complete || "$(cat index/complete)" != "$expected $stamp" ]]; then
    zstd -dcq --long=31 "$input" |
        LC_ALL=C grep -aE '^\{"(in"|axiom"|def"|thm"|opaque"|quot"|inductive")' |
        zstd -q -T1 -3 -f -o index/names-declarations.zst
    zstd -dcq index/names-declarations.zst | python3 "$here/catalog.py" index
    zstd -dcq index/names-declarations.zst | python3 "$here/dictionary.py" index
    zstd -dcq --long=31 "$input" | ./slice index index
    printf '%s %s\n' "$expected" "$stamp" > index/complete
fi
python3 "$here/roots.py" index "$target" | ./slice mark index "$target-$mode" "$mode"
