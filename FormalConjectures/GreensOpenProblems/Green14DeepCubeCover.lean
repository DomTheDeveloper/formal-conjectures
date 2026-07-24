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

import FormalConjectures.GreensOpenProblems.Green14NestedCubeCover

/-!
# Third-level cube coverage for hard `W(3,20)` grandchildren

The third computational split fixes DIMACS variables `199, 200, 201`, which are
Lean variables `198, 199, 200`.  Refuting all eight assignments to those three
variables refutes the corresponding grandchild formula.
-/

namespace Green14.DeepCubeCover

open Green14.NestedCubeCover

/-- Unit clauses for the profiled third-level split. -/
def thirdUnits (bits : Fin 3 → Bool) : Std.Sat.CNF Nat :=
  [[(198, bits 0)], [(199, bits 1)], [(200, bits 2)]]

/-- A two-level grandchild with one complete third-level assignment appended. -/
def greatGrandchildCNF (parent : Fin 6 → Bool) (child third : Fin 3 → Bool) :
    Std.Sat.CNF Nat :=
  grandchildCNF parent child ++ thirdUnits third

/-- An assignment satisfies the third-level unit clauses selected from itself. -/
theorem eval_thirdUnits_self (assignment : Nat → Bool) :
    Std.Sat.CNF.eval assignment
      (thirdUnits fun j => assignment (198 + j.1)) = true := by
  simp [thirdUnits, Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval]

/-- Exhausting all eight third-level assignments proves the grandchild UNSAT. -/
theorem grandchildCNF_unsat_of_all_thirds
    (parent : Fin 6 → Bool) (child : Fin 3 → Bool)
    (hthirds : ∀ third : Fin 3 → Bool,
      (greatGrandchildCNF parent child third).Unsat) :
    (grandchildCNF parent child).Unsat := by
  intro assignment
  cases hgrandchild : Std.Sat.CNF.eval assignment (grandchildCNF parent child) with
  | false => exact hgrandchild
  | true =>
      let third : Fin 3 → Bool := fun j => assignment (198 + j.1)
      have hunits : Std.Sat.CNF.eval assignment (thirdUnits third) = true := by
        simpa [third] using eval_thirdUnits_self assignment
      have hgreat := hthirds third assignment
      have hfalse : False := by
        simpa [greatGrandchildCNF, Std.Sat.CNF.eval_append,
          hgrandchild, hunits] using hgreat
      exact hfalse.elim

end Green14.DeepCubeCover
