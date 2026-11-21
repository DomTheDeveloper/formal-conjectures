#!/usr/bin/env bash
# Publish the supplied verified files under their existing tag. Release assets are immutable here.
set -euo pipefail
tag=$1
title=$2
notes=$3
shift 3
if ! gh release view "$tag" >/dev/null 2>&1; then
    gh release create "$tag" --verify-tag --draft --prerelease --latest=false --title "$title" --notes-file "$notes"
fi
for path in "$@"; do
    name=$(basename "$path")
    sha="sha256:$(sha256sum "$path" | cut -d' ' -f1)"
    for delay in 0 5 15; do
        sleep "$delay"
        actual=$(gh release view "$tag" --json assets --jq ".assets[] | select(.name == \"$name\") | .digest")
        [[ "$actual" != "$sha" ]] || break
        if [[ -n "$actual" ]]; then echo "A different $name exists in $tag" >&2; exit 1; fi
        gh release upload "$tag" "$path" && break
    done
    actual=$(gh release view "$tag" --json assets --jq ".assets[] | select(.name == \"$name\") | .digest")
    [[ "$actual" == "$sha" ]]
done
gh release edit "$tag" --draft=false --prerelease --latest=false
