#!/bin/sh
set -eu

proof_directory=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
project_directory=$(dirname "$proof_directory")
cd "$project_directory"

project_lean_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$proof_directory:$project_lean_path"

compile_module() {
  source_file=$1
  lake env lean -o "${source_file%.lean}.olean" "$source_file"
}

lake build FormalConjectures.Paper.MonochromaticQuantumGraph
compile_module "$proof_directory/QuantumGraphCompactLRAT.lean"
compile_module "$proof_directory/QuantumGraphSemantic.lean"
compile_module "$proof_directory/QuantumGraphOrbitData.lean"
compile_module "$proof_directory/QuantumGraphOrbitBridge.lean"
compile_module "$proof_directory/QuantumGraphParityBridge.lean"

printf '%s\n' "$proof_directory"/QuantumGraphCase*Certificate.lean |
  xargs -n 1 -P 4 sh -c '
    source_file=$1
    lake env lean -o "${source_file%.lean}.olean" "$source_file"
  ' sh

compile_module "$proof_directory/QuantumGraphAllCases.lean"
compile_module "$proof_directory/QuantumGraphGlobal.lean"
lake env lean "$proof_directory/QuantumGraphAxiomAudit.lean"
