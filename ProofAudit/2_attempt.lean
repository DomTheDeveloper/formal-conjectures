/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Written on the Wall II - Conjecture 2

Audit copy. Contains two explicit proof holes.
-/

namespace WrittenOnTheWallII.GraphConjecture2

open Classical SimpleGraph

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha] [Nontrivial alpha]

/-- The double-counting half of the mathematical proof. -/
private theorem two_mul_averageIndepNeighbors_le_adjacent_neighbor_union
    (G : SimpleGraph alpha) (hG : G.Connected) :
    Exists fun x : alpha =>
      Exists fun y : alpha =>
        And (G.Adj x y)
          (2 * averageIndepNeighbors G <=
            (Set.ncard (G.neighborSet x ∪ G.neighborSet y) : Real)) := by
  sorry

/-- The double-star / spanning-tree-extension half of the proof. -/
private theorem adjacent_neighbor_union_le_Ls_add_two
    (G : SimpleGraph alpha) (hG : G.Connected)
    {x y : alpha} (hxy : G.Adj x y) :
    (Set.ncard (G.neighborSet x ∪ G.neighborSet y) : Real) <= Ls G + 2 := by
  sorry

/-- WOWII Conjecture 2. -/
@[category research open, AMS 5]
theorem conjecture2 (G : SimpleGraph alpha) (hG : G.Connected) :
    2 * (averageIndepNeighbors G - 1) <= Ls G := by
  obtain ⟨x, y, hxy, havg⟩ :=
    two_mul_averageIndepNeighbors_le_adjacent_neighbor_union G hG
  have htree := adjacent_neighbor_union_le_Ls_add_two G hG hxy
  linarith

#print axioms conjecture2

end WrittenOnTheWallII.GraphConjecture2
