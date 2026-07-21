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

import FormalConjectures.WrittenOnTheWallII.GraphConjecture100Complete

/-!
# Written on the Wall II - Conjecture 100

This file exposes the complete source-aligned proof under the exact canonical
namespace and theorem signature used by Formal Conjectures.
-/

namespace WrittenOnTheWallII.GraphConjecture100

open Classical SimpleGraph

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
For every finite nontrivial connected simple graph `G`, its independence number
is bounded by the ceiling involving the maximum local independence number and
the Euclidean norm of the complement degree sequence.
-/
@[category research solved, AMS 5]
theorem conjecture100 (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤
      ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
  exact GraphConjecture100Complete.conjecture100 G h

#print axioms WrittenOnTheWallII.GraphConjecture100.conjecture100

end WrittenOnTheWallII.GraphConjecture100
