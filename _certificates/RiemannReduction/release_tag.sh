#!/usr/bin/env bash
# A release tag must be created while its target is the current branch tip.
set -euo pipefail
tag=$1
if gh api "repos/$GH_REPO/git/ref/tags/$tag" --silent 2>/dev/null; then exit 0; fi
tip=$(gh api "repos/$GH_REPO/git/ref/heads/rh/unconditional-reduction" --jq .object.sha)
gh api --method POST "repos/$GH_REPO/git/refs" -f "ref=refs/tags/$tag" -f "sha=$tip" --silent
test "$(gh api "repos/$GH_REPO/git/ref/tags/$tag" --jq .object.sha)" = "$tip"
echo "Reserved $tag at $tip"
