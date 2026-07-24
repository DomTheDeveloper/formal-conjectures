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

import FormalConjectures.GreensOpenProblems.Green14CNFEncoding

/-!
# Integer-mask cube coverage for the `W(3,20)` certificate

The external jobs name first-level cubes by masks `0, ..., 63`. Bit `j` fixes
DIMACS variable `193 + j`, corresponding to Lean variable `192 + j`. This file
uses the same integer masks directly, eliminating any ambiguity between external
artifact names and Lean functions.
-/

namespace Green14.MaskCubeCover

open Green14.CNFEncoding

/-- Encode six Boolean values as a little-endian integer mask. -/
def mask6 (b0 b1 b2 b3 b4 b5 : Bool) : Nat :=
  b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
    16 * b4.toNat + 32 * b5.toNat

theorem mask6_lt_64 (b0 b1 b2 b3 b4 b5 : Bool) :
    mask6 b0 b1 b2 b3 b4 b5 < 64 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;> decide

theorem mask6_testBit_zero (b0 b1 b2 b3 b4 b5 : Bool) :
    (mask6 b0 b1 b2 b3 b4 b5).testBit 0 = b0 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;> decide

theorem mask6_testBit_one (b0 b1 b2 b3 b4 b5 : Bool) :
    (mask6 b0 b1 b2 b3 b4 b5).testBit 1 = b1 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;> decide

theorem mask6_testBit_two (b0 b1 b2 b3 b4 b5 : Bool) :
    (mask6 b0 b1 b2 b3 b4 b5).testBit 2 = b2 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;> decide

theorem mask6_testBit_three (b0 b1 b2 b3 b4 b5 : Bool) :
    (mask6 b0 b1 b2 b3 b4 b5).testBit 3 = b3 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;> decide

theorem mask6_testBit_four (b0 b1 b2 b3 b4 b5 : Bool) :
    (mask6 b0 b1 b2 b3 b4 b5).testBit 4 = b4 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;> decide

theorem mask6_testBit_five (b0 b1 b2 b3 b4 b5 : Bool) :
    (mask6 b0 b1 b2 b3 b4 b5).testBit 5 = b5 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;> decide

/-- Unit clauses for exactly the external mask numbering. -/
def cubeUnitsMask (mask : Nat) : Std.Sat.CNF Nat :=
  [[(192, mask.testBit 0)], [(193, mask.testBit 1)],
   [(194, mask.testBit 2)], [(195, mask.testBit 3)],
   [(196, mask.testBit 4)], [(197, mask.testBit 5)]]

/-- The exact base formula plus the first-level external cube mask. -/
def cubeCNFMask (mask : Nat) : Std.Sat.CNF Nat :=
  w320CNF ++ cubeUnitsMask mask

/-- An assignment satisfies the mask reconstructed from its six selected bits. -/
theorem eval_cubeUnitsMask_self (assignment : Nat → Bool) :
    let mask := mask6 (assignment 192) (assignment 193) (assignment 194)
      (assignment 195) (assignment 196) (assignment 197)
    Std.Sat.CNF.eval assignment (cubeUnitsMask mask) = true := by
  dsimp
  simp [cubeUnitsMask, Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval,
    mask6_testBit_zero, mask6_testBit_one, mask6_testBit_two,
    mask6_testBit_three, mask6_testBit_four, mask6_testBit_five]

/-- Refuting all 64 externally numbered cubes refutes the unrestricted CNF. -/
theorem w320CNF_unsat_of_all_masks
    (hcubes : ∀ mask : Fin 64, (cubeCNFMask mask.1).Unsat) :
    w320CNF.Unsat := by
  intro assignment
  cases hbase : Std.Sat.CNF.eval assignment w320CNF with
  | false => exact hbase
  | true =>
      let maskNat := mask6 (assignment 192) (assignment 193) (assignment 194)
        (assignment 195) (assignment 196) (assignment 197)
      let mask : Fin 64 := ⟨maskNat, mask6_lt_64 _ _ _ _ _ _⟩
      have hunits :
          Std.Sat.CNF.eval assignment (cubeUnitsMask maskNat) = true := by
        simpa [maskNat] using eval_cubeUnitsMask_self assignment
      have hcube := hcubes mask assignment
      have hfalse : False := by
        simpa [cubeCNFMask, mask, Std.Sat.CNF.eval_append,
          hbase, hunits] using hcube
      exact hfalse.elim

/-- The 64 external mask certificates imply the exact catalog value. -/
theorem W_3_20_eq_389_of_all_masks
    (hcubes : ∀ mask : Fin 64, (cubeCNFMask mask.1).Unsat) :
    Green14.W 3 20 = 389 := by
  exact W_3_20_eq_389_of_w320CNF_unsat
    (w320CNF_unsat_of_all_masks hcubes)

end Green14.MaskCubeCover
