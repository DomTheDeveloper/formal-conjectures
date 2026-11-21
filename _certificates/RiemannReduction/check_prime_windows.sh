#!/usr/bin/env bash
# Recompile the prime-window theorem, export its full dependency closure and check the shorter certificate.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(realpath "$1")
scratch=$(realpath -m "$2")
exporter=$(realpath "$3")
native=$(realpath "$4")
certified=$(realpath "$5")
mkdir -p "$scratch/src/RiemannReduction" "$scratch/objects/RiemannReduction" "$scratch/index"
cp "$here/PrimeWindows.lean" "$scratch/src/RiemannReduction/PrimeWindows.lean"
(
    cd "$project"
    lake env lean -R "$scratch/src" -o "$scratch/objects/RiemannReduction/PrimeWindows.olean" \
      "$scratch/src/RiemannReduction/PrimeWindows.lean"
    lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec "$2" RiemannReduction.PrimeWindows -- RiemannReduction.rh_of_prime_windows' \
      bash "$scratch/objects" "$exporter" > "$scratch/original.ndjson"
)
g++ -std=c++20 -O3 -DNDEBUG -Wall -Wextra -Werror "$here/slice.cpp" -lzstd -o "$scratch/slice"
LC_ALL=C grep -aE '^\{"(in"|axiom"|def"|thm"|opaque"|quot"|inductive")' "$scratch/original.ndjson" |
    zstd -q -T1 -5 -f -o "$scratch/index/names-declarations.zst"
zstd -dcq "$scratch/index/names-declarations.zst" | python3 "$here/catalog.py" "$scratch/index"
zstd -dcq "$scratch/index/names-declarations.zst" | python3 "$here/dictionary.py" "$scratch/index"
"$scratch/slice" index "$scratch/index" < "$scratch/original.ndjson"
python3 "$here/roots.py" "$scratch/index" RiemannReduction.rh_of_prime_windows |
    "$scratch/slice" mark "$scratch/index" "$scratch/selection" share
python3 "$here/dictionary.py" "$scratch/index" "$scratch/selection"
"$scratch/slice" emit "$scratch/index" "$scratch/selection" < "$scratch/original.ndjson" |
    "$scratch/slice" intern 22 > "$scratch/windows.ndjson"
"$native" --from-export "$scratch/windows.ndjson"
"$certified" --verified --jobs=2 "$scratch/windows.ndjson"
sha256sum "$scratch/windows.ndjson"
