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

import FormalConjectures.GreensOpenProblems.Green14MaskCubeCover

/-!
# Integer-mask recursive cube coverage

This module mirrors the external names `cube-parent-child-third` exactly.
Second-level masks fix DIMACS variables `190..192` and third-level masks fix
DIMACS variables `199..201`.
-/

namespace Green14.MaskDeepCubeCover

open Green14.CNFEncoding
open Green14.MaskCubeCover

/-- Encode three Boolean values as a little-endian mask in `0, ..., 7`. -/
def mask3 (b0 b1 b2 : Bool) : Nat :=
  boolNat b0 + 2 * boolNat b1 + 4 * boolNat b2

theorem mask3_lt_8 (b0 b1 b2 : Bool) : mask3 b0 b1 b2 < 8 := by
  cases b0 <;> cases b1 <;> cases b2 <;> decide

theorem mask3_testBit_zero (b0 b1 b2 : Bool) :
    (mask3 b0 b1 b2).testBit 0 = b0 := by
  cases b0 <;> cases b1 <;> cases b2 <;> decide

theorem mask3_testBit_one (b0 b1 b2 : Bool) :
    (mask3 b0 b1 b2).testBit 1 = b1 := by
  cases b0 <;> cases b1 <;> cases b2 <;> decide

theorem mask3_testBit_two (b0 b1 b2 : Bool) :
    (mask3 b0 b1 b2).testBit 2 = b2 := by
  cases b0 <;> cases b1 <;> cases b2 <;> decide

/-- Second-level external mask clauses, fixing Lean variables `189..191`. -/
def childUnitsMask (mask : Nat) : Std.Sat.CNF Nat :=
  [[(189, mask.testBit 0)], [(190, mask.testBit 1)],
   [(191, mask.testBit 2)]]

/-- A first-level parent plus one second-level external mask. -/
def grandchildCNFMask (parent child : Nat) : Std.Sat.CNF Nat :=
  cubeCNFMask parent ++ childUnitsMask child

/-- An assignment satisfies its reconstructed second-level mask. -/
theorem eval_childUnitsMask_self (assignment : Nat → Bool) :
    let mask := mask3 (assignment 189) (assignment 190) (assignment 191)
    Std.Sat.CNF.eval assignment (childUnitsMask mask) = true := by
  dsimp
  simp [childUnitsMask, Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval,
    mask3_testBit_zero, mask3_testBit_one, mask3_testBit_two]

/-- Eight child-mask refutations imply the corresponding parent refutation. -/
theorem cubeCNFMask_unsat_of_all_child_masks (parent : Nat)
    (hchildren : ∀ child : Fin 8,
      (grandchildCNFMask parent child.1).Unsat) :
    (cubeCNFMask parent).Unsat := by
  intro assignment
  cases hparent : Std.Sat.CNF.eval assignment (cubeCNFMask parent) with
  | false => exact hparent
  | true =>
      let childNat := mask3 (assignment 189) (assignment 190) (assignment 191)
      let child : Fin 8 := ⟨childNat, mask3_lt_8 _ _ _⟩
      have hunits :
          Std.Sat.CNF.eval assignment (childUnitsMask childNat) = true := by
        simpa [childNat] using eval_childUnitsMask_self assignment
      have hgrandchild := hchildren child assignment
      have hfalse : False := by
        simpa [grandchildCNFMask, child, Std.Sat.CNF.eval_append,
          hparent, hunits] using hgrandchild
      exact hfalse.elim

/-- Third-level external mask clauses, fixing Lean variables `198..200`. -/
def thirdUnitsMask (mask : Nat) : Std.Sat.CNF Nat :=
  [[(198, mask.testBit 0)], [(199, mask.testBit 1)],
   [(200, mask.testBit 2)]]

/-- A parent-child pair plus one third-level external mask. -/
def greatGrandchildCNFMask (parent child third : Nat) : Std.Sat.CNF Nat :=
  grandchildCNFMask parent child ++ thirdUnitsMask third

/-- An assignment satisfies its reconstructed third-level mask. -/
theorem eval_thirdUnitsMask_self (assignment : Nat → Bool) :
    let mask := mask3 (assignment 198) (assignment 199) (assignment 200)
    Std.Sat.CNF.eval assignment (thirdUnitsMask mask) = true := by
  dsimp
  simp [thirdUnitsMask, Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval,
    mask3_testBit_zero, mask3_testBit_one, mask3_testBit_two]

/-- Eight third-mask refutations imply the corresponding grandchild refutation. -/
theorem grandchildCNFMask_unsat_of_all_third_masks (parent child : Nat)
    (hthirds : ∀ third : Fin 8,
      (greatGrandchildCNFMask parent child third.1).Unsat) :
    (grandchildCNFMask parent child).Unsat := by
  intro assignment
  cases hgrandchild :
      Std.Sat.CNF.eval assignment (grandchildCNFMask parent child) with
  | false => exact hgrandchild
  | true =>
      let thirdNat := mask3 (assignment 198) (assignment 199) (assignment 200)
      let third : Fin 8 := ⟨thirdNat, mask3_lt_8 _ _ _⟩
      have hunits :
          Std.Sat.CNF.eval assignment (thirdUnitsMask thirdNat) = true := by
        simpa [thirdNat] using eval_thirdUnitsMask_self assignment
      have hgreat := hthirds third assignment
      have hfalse : False := by
        simpa [greatGrandchildCNFMask, third, Std.Sat.CNF.eval_append,
          hgrandchild, hunits] using hgreat
      exact hfalse.elim

end Green14.MaskDeepCubeCover
