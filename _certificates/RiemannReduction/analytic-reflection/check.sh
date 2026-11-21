#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=$(realpath "$1")
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cd "$project"
[[ $(lean --version) == "Lean (version 4.33.1,"* ]]
package_paths=$(lake env printenv LEAN_PATH)
external=()
IFS=: read -r -a paths <<< "$package_paths"
math_revision=0df444a360eaa60ab8c11dca51a86af692955474
for p in "${paths[@]}"; do
  p=$(realpath -m "$p")
  if [[ $p == *'/.lake/packages/'* || $p == "$project/.lake/build/lib/lean" && -d "$p/Mathlib" ]]; then
    [[ ! -e "$p/Development" && ! -e "$p/Main.olean" ]]
    external+=("$p")
    if [[ -d "$p/Mathlib" ]]; then
      [[ $(git -C "$p" rev-parse HEAD) == "$math_revision" ]]
    fi
  fi
done
external_path=$(IFS=:; echo "${external[*]}")
export LEAN_PATH="$work:$external_path"
cd "$work"
cp "$here/OriginalReflection.lean" "$here/ZetaReflection.lean" .
for name in OriginalReflection ZetaReflection; do
  case "$name" in
    OriginalReflection) theorem=UpperTheory.riemannHypothesis_of_everyCharacter ;;
    ZetaReflection) theorem=RHReflection.iff_upper_right ;;
  esac
  lean -j1 -DautoImplicit=false -DwarningAsError=true -DmaxHeartbeats=4000000 -R . -o "$name.olean" "$name.lean" | tee "$name.log"
  grep -Fx "'$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$name.log"
  leanchecker -v "$name"
done
