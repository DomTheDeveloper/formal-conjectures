#!/usr/bin/env bash
set +e

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LOG="$ROOT/binder/lean.log"
STATUS="$ROOT/binder/status.txt"
AXIOMS="$ROOT/binder/VoronovskajaAxioms.lean"
: > "$LOG"

{
  echo "source_commit=9e86fc07e4af4bb53e62503bf5fcfefde4ea4bcf"
  echo "started_at=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "lean_toolchain=$(cat "$ROOT/lean-toolchain")"
} > "$STATUS"

cd "$ROOT" || exit 1

printf '\n== Toolchain ==\n' | tee -a "$LOG"
lean --version 2>&1 | tee -a "$LOG"
lake --version 2>&1 | tee -a "$LOG"

printf '\n== Placeholder guard ==\n' | tee -a "$LOG"
grep -R -nE '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)|^[[:space:]]*axiom[[:space:]]' \
  FormalConjectures/Paper/Voronovskaja*.lean \
  FormalConjecturesForMathlib/Probability/CentralLimitTheorem.lean \
  FormalConjecturesForMathlib/Probability/CDFConvergence.lean \
  FormalConjecturesForMathlib/Probability/Distributions/Bernoulli.lean \
  FormalConjecturesForMathlib/Probability/Distributions/Binomial.lean \
  FormalConjecturesForMathlib/Probability/Distributions/StandardizedBinomial*.lean \
  FormalConjecturesForMathlib/Probability/Distributions/PoweredGaussian.lean \
  FormalConjecturesForMathlib/Probability/Distributions/PoweredBinomial*.lean \
  FormalConjecturesForMathlib/Order/Filter/ENNReal.lean \
  FormalConjecturesForMathlib/MeasureTheory/Measure/LevyConvergence.lean \
  FormalConjecturesForMathlib/MeasureTheory/Measure/CharacteristicFunction/TaylorExpansion.lean \
  >> "$LOG" 2>&1
placeholder_code=$?
if [[ $placeholder_code -eq 0 ]]; then
  echo 'placeholder_guard=failed' >> "$STATUS"
  echo 'Proof placeholder or custom axiom declaration detected.' | tee -a "$LOG"
else
  echo 'placeholder_guard=passed' >> "$STATUS"
fi

printf '\n== Fetch pinned dependency cache ==\n' | tee -a "$LOG"
lake exe cache get 2>&1 | tee -a "$LOG"
cache_code=${PIPESTATUS[0]}
echo "cache_exit_code=$cache_code" >> "$STATUS"

printf '\n== Compile exact theorem ==\n' | tee -a "$LOG"
lake build FormalConjectures.Paper.VoronovskajaTypeFormula 2>&1 | tee -a "$LOG"
build_code=${PIPESTATUS[0]}
echo "build_exit_code=$build_code" >> "$STATUS"

cat > "$AXIOMS" <<'EOF'
import FormalConjectures.Paper.VoronovskajaTypeFormula
#print axioms VoronovskajaTypeFormula.voronovskaja_theorem.bernstein_operators
#print axioms VoronovskajaTypeFormula.voronovskaja_theorem.bezier_bernstein_operators
#print axioms VoronovskajaTypeFormula.tendsto_bezierBernstein_all
#print axioms VoronovskajaTypeFormula.tendsto_classical_bezierBernstein_all
EOF

printf '\n== Kernel axiom audit ==\n' | tee -a "$LOG"
lake env lean "$AXIOMS" 2>&1 | tee -a "$LOG"
axiom_code=${PIPESTATUS[0]}
echo "axiom_audit_exit_code=$axiom_code" >> "$STATUS"

if grep -E 'sorryAx|Lean\.trustCompiler|Lean\.ofReduce' "$LOG" >/dev/null; then
  disallowed=1
  echo 'disallowed_axiom_detected=yes' >> "$STATUS"
else
  disallowed=0
  echo 'disallowed_axiom_detected=no' >> "$STATUS"
fi

if [[ $placeholder_code -ne 0 && $cache_code -eq 0 && $build_code -eq 0 && $axiom_code -eq 0 && $disallowed -eq 0 ]]; then
  echo 'kernel_verification=passed' >> "$STATUS"
else
  echo 'kernel_verification=failed' >> "$STATUS"
fi

echo "finished_at=$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$STATUS"
cat "$STATUS" | tee -a "$LOG"
exit 0
