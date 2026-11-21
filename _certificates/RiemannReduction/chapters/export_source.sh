#!/usr/bin/env bash
# Re-elaborate the chapters. The complete checker separately supplies and checks every original proof body.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
original=$(realpath "$1")
build=$(realpath "$2")
project=$(realpath "$3")
exporter=$(realpath "$4")
scratch=$(realpath -m "$5")
mkdir -p "$scratch"/{objects/RH17,src/RH17,parser}
test "$(git -C "$project" rev-parse HEAD:src)" = b41b516b1f7baee4d83ced235ecc71fd43c97695
test "$(git -C "$exporter" rev-parse HEAD)" = 15f6055e299ad5b89345e533cc2192f4cc00f659
python3 - "$here/arithmetic-names.txt" "$build/index/names.tsv" > "$scratch/provider-ids.txt" <<'PY'
from pathlib import Path
import sys
names = set(Path(sys.argv[1]).read_text().splitlines())
with open(sys.argv[2]) as f:
    for line in f:
        number, _, name = line.rstrip('\n').split('\t', 2)
        if name in names:
            names.remove(name)
            print(number)
if names:
    raise ValueError(f'Missing arithmetic providers: {names}')
PY
"$build/slice" types "$build/index" "$scratch/interfaces" < "$scratch/provider-ids.txt"
python3 "$here/../dictionary.py" "$build/index" "$scratch/interfaces"
zstd -dcq --long=31 "$original" | "$build/slice" emit "$build/index" "$scratch/interfaces" |
    zstd -q -T1 -5 -f -o "$scratch/interfaces.ndjson.zst"
cp "$exporter/Export/Parse.lean" "$scratch/parser/ParseExport33.lean"
(
    cd "$scratch/parser"
    lean -R . -o ParseExport33.olean ParseExport33.lean
)
cp "$here"/RH17/S*.lean "$scratch/src/RH17/"
# Only the local elaboration context changes. Preserve the last chapter's declarations byte for byte.
python3 - "$scratch/src/RH17/S17_RiemannHypothesis.lean" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1])
lines = p.read_bytes().splitlines(keepends=True)
if not all(s.startswith(b'import Development.AutomorphicArithmetic.') for s in lines[:4]) or not lines[4].startswith(b'import RH17.'):
    raise ValueError('Unexpected original provider imports')
p.write_bytes(b'import RHChapterContext\n'+b''.join(lines[4:]))
PY
cd "$project"
export LEAN_PATH="$scratch/objects:$scratch/parser:$(lake env printenv LEAN_PATH)"
for file in "$scratch"/src/RH17/S*.lean; do
    name=$(basename "$file" .lean)
    if [[ "$name" == S17_RiemannHypothesis ]]; then
        export RH_INTERFACE_OUTPUT="$scratch/objects/RHChapterContext.olean"
        zstd -dcq "$scratch/interfaces.ndjson.zst" |
            lean --tstack=65536 -R "$here" "$here/MakeChapterContext.lean"
    fi
    lean -j1 --tstack=65536 -DwarningAsError=true -R "$scratch/src" -o "$scratch/objects/RH17/$name.olean" "$file"
done
# The upstream inventory stops export at every authentic external constant, including the arithmetic inputs.
# The linker rejects extra axioms; the subsequent whole-proof check restores those inputs' actual proofs.
export LEAN_PATH="$exporter/.lake/build/lib/lean:$LEAN_PATH"
lean --run "$here/ThinExport.lean" "$build/index/names.tsv" RH17.S17_RiemannHypothesis \
    RH17.riemannHypothesisFromPublishedArithmetic |
    zstd -q -T1 -9 -f -o "$scratch/chapters.ndjson.zst"
