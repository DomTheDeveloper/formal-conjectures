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

import FormalConjectures.ErdosProblems.«332»

/-!
# Literal solution of Erdős Problem 332's answer placeholder

The catalog asks for an unrestricted predicate on sets of naturals that is
sufficient for bounded gaps in `D_A A`. Choosing the predicate to be constantly
false makes the implication vacuous. This proves that the literal answer format
does not encode the intended task of finding a meaningful sufficient condition.
-/

namespace Erdos332

/-- The literal statement admits the vacuous sufficient condition `False`. -/
@[category research solved, AMS 11]
theorem erdos_332_literal_solution (A : Set ℕ) :
    ∃ condition : Set ℕ → Prop, condition A → HasBoundedGaps (D_A A) := by
  refine ⟨fun _ => False, ?_⟩
  intro h
  exact h.elim

#print axioms erdos_332_literal_solution

end Erdos332
