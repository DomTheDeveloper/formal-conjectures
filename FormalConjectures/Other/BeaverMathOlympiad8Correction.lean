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

import FormalConjectures.Other.BeaverMathOlympiad

/-!
# Beaver Math Olympiad Problem 8: faithful reduced dynamics

The previously encoded two-branch `ℕ` recurrence uses truncated subtraction in the branch
`a - b / 2 - 3`.  At the first state where `a - b / 2 = 2`, that encoding moves
`(675, 1347)` to `(0, 2028)`.

The machine-derived reduction has a separate difference-two transition and instead moves
`(675, 1347)` to `(2, 2030)`.  Difference one is the halting condition.  This file records the
corrected transition system while keeping BMO #8 open.

Formalization and audit by Dominic Dabish with ProofOrchestrator.
-/

namespace BeaverMathOlympiad

/-- A state of the corrected reduced BMO #8 dynamics. -/
abbrev BMO8State := ℕ × ℕ

/-- The halting predicate in the reduced BMO #8 dynamics. -/
def bmo8Halting (s : BMO8State) : Prop :=
  s.1 = s.2 / 2 + 1

/--
One step of the machine-faithful reduced dynamics.

The halting state is made absorbing only to obtain a total function.  Before the halting state:
* difference two uses the exceptional `(2, 3 * ceil(b/2) + 8)` transition;
* difference at least three uses the ordinary subtraction branch;
* nonpositive difference uses the expansion branch.
-/
def bmo8FaithfulStep : BMO8State → BMO8State
  | (a, b) =>
      if a = b / 2 + 1 then
        (a, b)
      else if a = b / 2 + 2 then
        (2, 3 * ((b + 1) / 2) + 8)
      else if b / 2 + 3 ≤ a then
        (a - b / 2 - 3, 3 * ((b + 1) / 2) + 6)
      else
        (3 * a + 5, b - 2 * a)

/-- The original truncated-`Nat` transition, retained only for comparison. -/
def bmo8TruncatedNatStep : BMO8State → BMO8State
  | (a, b) =>
      if b / 2 < a then
        (a - b / 2 - 3, 3 * ((b + 1) / 2) + 6)
      else
        (3 * a + 5, b - 2 * a)

/-- The first boundary state exposes the semantic difference between the two models. -/
@[category test, AMS 5 11 68]
theorem bmo8_first_boundary_transition :
    bmo8FaithfulStep (675, 1347) = (2, 2030) ∧
    bmo8TruncatedNatStep (675, 1347) = (0, 2028) := by
  native_decide

/-- The corrected BMO #8 statement remains open. -/
@[category research open, AMS 5 11 68]
theorem beaver_math_olympiad_problem_8_corrected : answer(sorry) ↔
    ∃ n : ℕ,
      bmo8Halting ((bmo8FaithfulStep^[n]) (10, 12)) := by
  sorry

end BeaverMathOlympiad
