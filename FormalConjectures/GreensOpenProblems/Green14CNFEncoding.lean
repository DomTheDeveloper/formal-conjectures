/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.GreensOpenProblems.Green14PositiveCertificateBridge
import FormalConjectures.GreensOpenProblems.Green14UpperOrderBridge
import Std.Tactic.BVDecide.LRAT

/-!
# Exact CNF encoding for `W(3,20) ≤ 389`

Variables are zero-based in Lean. Variable `i` is the color of the catalog
point `i + 1`. The LRAT conversion shifts these to one-based DIMACS variables.

For every `k`-term progression and target color `color`, the generated clause
contains literals with polarity `!color`. It is satisfied exactly when at least
one term of the progression has the opposite color.
-/

namespace Green14.CNFEncoding

open Green14.FunctionCertificateBridge
open Green14.PositiveCertificateBridge

/-- The CNF forbidding monochromatic `k`-term progressions of `color` in the
zero-based interval `{0, ..., N - 1}`. -/
def apAvoidanceCNF (N k : Nat) (color : Bool) : Std.Sat.CNF Nat :=
  (List.range N).flatMap fun a =>
    (List.range ((N - 1 - a) / (k - 1))).map fun d0 =>
      let d := d0 + 1
      (List.range k).map fun i => (a + i * d, !color)

/-- The unrestricted exact SAT instance for the upper bound `W(3,20) ≤ 389`. -/
def w320CNF : Std.Sat.CNF Nat :=
  apAvoidanceCNF 389 3 false ++ apAvoidanceCNF 389 20 true

/-- The generated instance has the canonical 41,426 clauses. -/
theorem w320CNF_clause_count : w320CNF.length = 41426 := by
  decide

private theorem opposite_of_ne {x color : Bool} (h : x ≠ color) : x = !color := by
  cases x <;> cases color <;> simp_all

/-- A negative direct AP check satisfies every clause in the corresponding
avoidance CNF. -/
theorem eval_apAvoidanceCNF_eq_true
    {N k : Nat} {coloring : Nat → Bool} {color : Bool}
    (hk : 2 ≤ k) (hcheck : hasAP N k coloring color = false) :
    Std.Sat.CNF.eval coloring (apAvoidanceCNF N k color) = true := by
  rw [Std.Sat.CNF.eval, List.all_eq_true]
  intro clause hclause
  rcases List.mem_flatMap.mp hclause with ⟨a, ha, hinner⟩
  rcases List.mem_map.mp hinner with ⟨d0, hd0, rfl⟩
  have haN : a < N := by simpa using ha
  let d := d0 + 1
  have hdpos : 0 < d := by simp [d]
  have hkden : 0 < k - 1 := by omega
  have hd0lt : d0 < (N - 1 - a) / (k - 1) := by simpa using hd0
  have hdle : d ≤ (N - 1 - a) / (k - 1) := by
    simpa [d] using hd0lt
  have hmul : d * (k - 1) ≤ N - 1 - a :=
    (Nat.le_div_iff_mul_le hkden).mp hdle
  have hend : a + (k - 1) * d < N := by
    rw [Nat.mul_comm] at hmul
    omega
  obtain ⟨i, hi, hmismatch⟩ :=
    exists_mismatch_of_hasAP_eq_false hk hcheck haN hdpos hend
  rw [Std.Sat.CNF.Clause.eval]
  apply List.any_of_mem (by simpa using hi)
  have hopposite : coloring (a + i * d) = !color := opposite_of_ne hmismatch
  simp [d, hopposite]

/-- If both direct AP checkers are negative, the complete `W(3,20)` CNF is
satisfied by the coloring. -/
theorem eval_w320CNF_eq_true
    {coloring : Nat → Bool}
    (h3 : hasAP 389 3 coloring false = false)
    (h20 : hasAP 389 20 coloring true = false) :
    Std.Sat.CNF.eval coloring w320CNF = true := by
  rw [w320CNF, Std.Sat.CNF.eval_append]
  simp [eval_apAvoidanceCNF_eq_true (k := 3) (by omega) h3,
    eval_apAvoidanceCNF_eq_true (k := 20) (by omega) h20]

/-- Unsatisfiability of the exact CNF means every coloring triggers one of the
two direct arithmetic-progression checkers. -/
theorem direct_checks_complete_of_w320CNF_unsat
    (hunsat : w320CNF.Unsat) :
    ∀ coloring : Nat → Bool,
      hasAP 389 3 coloring false = true ∨
        hasAP 389 20 coloring true = true := by
  intro coloring
  by_cases h3 : hasAP 389 3 coloring false = true
  · exact Or.inl h3
  by_cases h20 : hasAP 389 20 coloring true = true
  · exact Or.inr h20
  have h3false : hasAP 389 3 coloring false = false := by
    cases h : hasAP 389 3 coloring false <;> simp_all
  have h20false : hasAP 389 20 coloring true = false := by
    cases h : hasAP 389 20 coloring true <;> simp_all
  have hevalTrue := eval_w320CNF_eq_true h3false h20false
  have hevalFalse := hunsat coloring
  rw [hevalTrue] at hevalFalse
  contradiction

/-- A checked UNSAT certificate for `w320CNF` proves the catalog's semantic
upper-bound statement. -/
theorem mem_389_of_w320CNF_unsat (hunsat : w320CNF.Unsat) :
    389 ∈ Green14.mixedMonoAPGuaranteeSet 3 20 := by
  exact mem_mixed_of_direct_checks (by omega) (by omega)
    (direct_checks_complete_of_w320CNF_unsat hunsat)

/-- A checked UNSAT certificate for the exact CNF, together with the existing
kernel-clean lower certificate, proves the exact value. -/
theorem W_3_20_eq_389_of_w320CNF_unsat (hunsat : w320CNF.Unsat) :
    Green14.W 3 20 = 389 := by
  exact Green14.W_3_20_eq_389_of_mem (mem_389_of_w320CNF_unsat hunsat)

end Green14.CNFEncoding
