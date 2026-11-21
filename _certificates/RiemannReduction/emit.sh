#!/usr/bin/env bash
# Write the complete, reindexed lean4export article on standard output.
set -euo pipefail
input=$(realpath "$1")
scratch=$(realpath "$2")
selection=$3
zstd -dcq --long=31 "$input" | "$scratch/slice" emit "$scratch/index" "$scratch/$selection"
