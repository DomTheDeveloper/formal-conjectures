#!/usr/bin/env bash
# Per-job setup for GitHub's ephemeral hosted machines.
set -euo pipefail
[[ ${GITHUB_ACTIONS:-false} == true ]]
case "$1" in
    space)
        sudo rm -rf /usr/local/lib/android /usr/share/dotnet /usr/share/swift /opt/ghc /opt/hostedtoolcache/CodeQL
        if [[ "${2:-0}" != 0 ]]; then
            path="$RUNNER_TEMP/module-replay.swap"
            sudo fallocate -l "$2"G "$path"
            sudo chmod 600 "$path"
            sudo mkswap "$path"
            sudo swapon "$path"
        fi ;;
    lean)
        curl -fsSL --retry 4 https://github.com/leanprover/elan/releases/download/v4.2.1/elan-x86_64-unknown-linux-gnu.tar.gz |
            tar xz -C "$RUNNER_TEMP"
        "$RUNNER_TEMP/elan-init" -y --default-toolchain leanprover/lean4:v4.33.1
        echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
        echo 'ELAN_TOOLCHAIN=leanprover/lean4:v4.33.1' >> "$GITHUB_ENV" ;;
    *) exit 2 ;;
esac
