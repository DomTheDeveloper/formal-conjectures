#!/bin/sh
set -eu

asset_name=quantum-graph-n6d3-clrat-v1.tar.zst
asset_url=https://github.com/infinityscroll/formal-conjectures/releases/download/quantum-graph-n6d3-int-v1/$asset_name
expected_sha256=c8855196dd1014ea59508078ed3e1f37f91dfff4e06e93317c98ef60a512f7c8
temporary_file=$(mktemp "${TMPDIR:-/tmp}/quantum-graph-certificates.XXXXXX")
trap 'rm -f "$temporary_file"' EXIT HUP INT TERM

curl --fail --location --output "$temporary_file" "$asset_url"

if command -v sha256sum >/dev/null 2>&1; then
  actual_sha256=$(sha256sum "$temporary_file" | awk '{print $1}')
else
  actual_sha256=$(shasum -a 256 "$temporary_file" | awk '{print $1}')
fi

if [ "$actual_sha256" != "$expected_sha256" ]; then
  printf '%s\n' "certificate checksum mismatch" >&2
  exit 1
fi

mkdir -p certificates
zstd --decompress --stdout "$temporary_file" | tar -xf -
printf '%s\n' "verified and extracted $asset_name"

