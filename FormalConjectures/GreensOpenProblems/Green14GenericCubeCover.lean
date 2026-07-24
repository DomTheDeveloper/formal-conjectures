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

import FormalConjectures.GreensOpenProblems.Green14MaskDeepCubeCover

/-!
# Generic three-variable cube coverage

Later certificate levels may use different variable triples on different hard
leaves. This theorem composes any exhaustive three-variable split, so adaptive
branching does not require a new logical proof for each selected triple.
-/

namespace Green14.GenericCubeCover

open Green14.MaskDeepCubeCover

/-- Unit clauses fixing arbitrary Lean variables `v0`, `v1`, and `v2` from a
little-endian mask in `0, ..., 7`. -/
def splitUnits3 (v0 v1 v2 mask : Nat) : Std.Sat.CNF Nat :=
  [[(v0, mask.testBit 0)], [(v1, mask.testBit 1)],
   [(v2, mask.testBit 2)]]

/-- Append one arbitrary three-variable split mask to a base CNF. -/
def splitCNF3 (base : Std.Sat.CNF Nat) (v0 v1 v2 mask : Nat) :
    Std.Sat.CNF Nat :=
  base ++ splitUnits3 v0 v1 v2 mask

/-- An assignment satisfies the split mask reconstructed from its own values. -/
theorem eval_splitUnits3_self (baseAssignment : Nat → Bool)
    (v0 v1 v2 : Nat) :
    let mask := mask3 (baseAssignment v0) (baseAssignment v1) (baseAssignment v2)
    Std.Sat.CNF.eval baseAssignment (splitUnits3 v0 v1 v2 mask) = true := by
  dsimp
  simp [splitUnits3, Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval,
    mask3_testBit_zero, mask3_testBit_one, mask3_testBit_two]

/-- Refuting all eight masks of any selected variable triple refutes the base
formula. No symmetry or heuristic assumption enters this theorem. -/
theorem unsat_of_all_split3 (base : Std.Sat.CNF Nat) (v0 v1 v2 : Nat)
    (hleaves : ∀ mask : Fin 8,
      (splitCNF3 base v0 v1 v2 mask.1).Unsat) :
    base.Unsat := by
  intro assignment
  cases hbase : Std.Sat.CNF.eval assignment base with
  | false => exact hbase
  | true =>
      let maskNat := mask3 (assignment v0) (assignment v1) (assignment v2)
      let mask : Fin 8 := ⟨maskNat, mask3_lt_8 _ _ _⟩
      have hunits :
          Std.Sat.CNF.eval assignment (splitUnits3 v0 v1 v2 maskNat) = true := by
        simpa [maskNat] using eval_splitUnits3_self assignment v0 v1 v2
      have hleaf := hleaves mask assignment
      have hfalse : False := by
        simpa [splitCNF3, mask, Std.Sat.CNF.eval_append,
          hbase, hunits] using hleaf
      exact hfalse.elim

end Green14.GenericCubeCover
