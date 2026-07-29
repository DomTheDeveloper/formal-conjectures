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

import FormalConjectures.GreensOpenProblems.Green14CubeCover

/-!
# Recursive cube coverage for hard `W(3,20)` leaves

The first decomposition fixes DIMACS variables `193, ..., 198`. Hard parent
cubes are split again on DIMACS variables `190, 191, 192`, which are Lean
variables `189, 190, 191`. This file proves that refuting all eight child
assignments refutes the parent cube.
-/

namespace Green14.NestedCubeCover

open Green14.CubeCover

/-- Unit clauses fixing the three secondary split variables. -/
def childUnits (bits : Fin 3 → Bool) : Std.Sat.CNF Nat :=
  [[(189, bits 0)], [(190, bits 1)], [(191, bits 2)]]

/-- A parent cube with one complete assignment to the secondary split. -/
def grandchildCNF (parent : Fin 6 → Bool) (child : Fin 3 → Bool) :
    Std.Sat.CNF Nat :=
  cubeCNF parent ++ childUnits child

/-- An assignment satisfies the unit clauses chosen from its own three selected
variable values. -/
theorem eval_childUnits_self (assignment : Nat → Bool) :
    Std.Sat.CNF.eval assignment
      (childUnits fun j => assignment (189 + j.1)) = true := by
  simp [childUnits, Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval]

/-- Exhausting all eight secondary assignments proves the parent cube UNSAT. -/
theorem cubeCNF_unsat_of_all_children
    (parent : Fin 6 → Bool)
    (hchildren : ∀ child : Fin 3 → Bool,
      (grandchildCNF parent child).Unsat) :
    (cubeCNF parent).Unsat := by
  intro assignment
  cases hparent : Std.Sat.CNF.eval assignment (cubeCNF parent) with
  | false => exact hparent
  | true =>
      let child : Fin 3 → Bool := fun j => assignment (189 + j.1)
      have hunits : Std.Sat.CNF.eval assignment (childUnits child) = true := by
        simpa [child] using eval_childUnits_self assignment
      have hgrandchild := hchildren child assignment
      have hfalse : False := by
        simpa [grandchildCNF, Std.Sat.CNF.eval_append, hparent, hunits]
          using hgrandchild
      exact hfalse.elim

end Green14.NestedCubeCover
