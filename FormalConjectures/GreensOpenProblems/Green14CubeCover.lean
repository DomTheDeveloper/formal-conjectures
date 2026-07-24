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
# Certified cube coverage for the `W(3,20)` upper bound

The external proof search fixes DIMACS variables `193, ..., 198`. The Lean CNF
is zero-based, so these are variables `192, ..., 197`. This file proves that
refuting every Boolean assignment to those six variables refutes the unrestricted
formula. No symmetry or heuristic assumption is involved: the cubes are the
complete assignment space `Fin 6 → Bool`.
-/

namespace Green14.CubeCover

open Green14.CNFEncoding

/-- Unit clauses fixing the six central variables according to a cube. -/
def cubeUnits (bits : Fin 6 → Bool) : Std.Sat.CNF Nat :=
  [[(192, bits 0)], [(193, bits 1)], [(194, bits 2)],
   [(195, bits 3)], [(196, bits 4)], [(197, bits 5)]]

/-- The exact base instance with one complete six-variable cube appended. -/
def cubeCNF (bits : Fin 6 → Bool) : Std.Sat.CNF Nat :=
  w320CNF ++ cubeUnits bits

/-- The unit clauses selected from an assignment are satisfied by that same
assignment. -/
theorem eval_cubeUnits_self (assignment : Nat → Bool) :
    Std.Sat.CNF.eval assignment
      (cubeUnits fun j => assignment (192 + j.1)) = true := by
  simp [cubeUnits, Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval]

/-- Complete cube coverage: if every assignment to the selected six variables
produces an UNSAT subproblem, the unrestricted base CNF is UNSAT. -/
theorem w320CNF_unsat_of_all_cubes
    (hcubes : ∀ bits : Fin 6 → Bool, (cubeCNF bits).Unsat) :
    w320CNF.Unsat := by
  intro assignment
  cases hbase : Std.Sat.CNF.eval assignment w320CNF with
  | false => exact hbase
  | true =>
      let bits : Fin 6 → Bool := fun j => assignment (192 + j.1)
      have hunits : Std.Sat.CNF.eval assignment (cubeUnits bits) = true := by
        simpa [bits] using eval_cubeUnits_self assignment
      have hcube := hcubes bits assignment
      have hfalse : False := by
        simpa [cubeCNF, Std.Sat.CNF.eval_append, hbase, hunits] using hcube
      exact hfalse.elim

/-- Refuting every six-variable cube proves the exact catalog value. -/
theorem W_3_20_eq_389_of_all_cubes
    (hcubes : ∀ bits : Fin 6 → Bool, (cubeCNF bits).Unsat) :
    Green14.W 3 20 = 389 := by
  exact W_3_20_eq_389_of_w320CNF_unsat
    (w320CNF_unsat_of_all_cubes hcubes)

end Green14.CubeCover
