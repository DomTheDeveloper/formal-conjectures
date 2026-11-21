#!/usr/bin/env bash
# Runs only on an ephemeral, standard GitHub-hosted Linux runner.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
test "${GITHUB_ACTIONS:-false}" = true
workdir="$RUNNER_TEMP/rh-verification"
mkdir -p "$workdir"
cd "$workdir"
# Reserve space for the checked proof and swap on this ephemeral runner.
sudo rm -rf /usr/local/lib/android /usr/share/dotnet /usr/share/swift /opt/ghc /opt/hostedtoolcache/CodeQL
sudo apt-get update -qq
sudo apt-get install -y -qq squashfs-tools libzstd-dev zstd
curl --fail --location --retry 4 --silent --show-error https://math.mit.edu/~drew/grh/solution.ndjson.zst -o original.zst
curl --fail --location --retry 4 --silent --show-error https://math.mit.edu/~drew/grh/challenge.ndjson.zst -o challenge.zst
zstd -dcq --long=31 challenge.zst > challenge.ndjson
echo 'bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9  challenge.ndjson' | sha256sum -c -
bash "$here/reduce.sh" original.zst build all share
article_index="$workdir/build"
selection=all-share
supplement=/dev/null
case "${2:-}" in
    protected)
        article_index="$workdir/guarded"
        bash "$here/guard_solution.sh" challenge.zst build "$article_index" ;;
    chapters)
        article_index="$workdir/chapters"
        selection=ordinary-chapters
        supplement="$article_index/extension.ndjson"
        bash "$here/chapters/prepare.sh" challenge.zst build "$article_index"
        python3 "$here/chapters/ordinary_challenge.py" challenge.zst challenge.ndjson
        echo '22e1398650efdc2d09930785e7ec5abf32e8311f1488d08d6e9def78455e7106  challenge.ndjson' | sha256sum -c - ;;
esac
mkdir -p empty mounted
# Give the checker a seekable, regular file without writing 60 GB of plain text.
cat > emit-pseudo.sh <<EOF
#!/usr/bin/env bash
set -euo pipefail
bash "$here/emit.sh" "$workdir/original.zst" "$article_index" "$selection"
cat "$supplement"
touch "$workdir/emit.ok"
EOF
chmod +x emit-pseudo.sh
mksquashfs empty article.sqfs -p "proof.ndjson f 0444 0 0 $workdir/emit-pseudo.sh" -comp zstd -b 1M -processors 2 -noappend -no-progress
test -f emit.ok
sudo mount -t squashfs -o loop,ro article.sqfs mounted
stat -c 'Reduced article: %s bytes' mounted/proof.ndjson
sha256sum mounted/proof.ndjson | tee reduced.sha256
rm -f original.zst build/index/edges.zst
free_gib=$(df -BG --output=avail . | tail -1 | tr -d ' G')
swap_gib=$((free_gib-6))
if ((swap_gib>80)); then swap_gib=80; fi
if ((swap_gib>0)); then
    sudo fallocate -l "${swap_gib}G" "$workdir/replay.swap"
    sudo chmod 600 "$workdir/replay.swap"
    sudo mkswap "$workdir/replay.swap"
    sudo swapon "$workdir/replay.swap"
fi
free -h
case "$1" in
    reference)
        /usr/bin/time -v leanchecker --from-export mounted/proof.ndjson ;;
    certified)
        /usr/bin/time -v "$RUNNER_TEMP/con-leche/.lake/build/bin/con-leche" --verified --jobs=4 --progress=100000 --compare challenge.ndjson mounted/proof.ndjson ;;
    *) exit 2 ;;
esac
