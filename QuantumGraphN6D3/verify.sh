#!/bin/sh
set -eu

proof_directory=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
project_directory=$(dirname "$proof_directory")
cd "$project_directory"

project_lean_path=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$proof_directory:$project_lean_path"

lake env lean "$proof_directory/QuantumGraphGlobal.lean"
lake env lean "$proof_directory/QuantumGraphAxiomAudit.lean"
