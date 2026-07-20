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

import WOWII.ZZGraphConjecture314C5BlowupClassification

/-!
Top-level assembly for the exact Formal Conjectures statement of WOWII Graph
Conjecture 314.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Exact proof candidate for the current repository theorem. -/
theorem conjecture314_proved [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4) :
    IsWellTotallyDominated G := by
  have hNoP5 : ∀ x0 x1 x2 x3 x4 : α,
      ¬FormsInducedP5 G x0 x1 x2 x3 x4 :=
    no_FormsInducedP5_of_largestInducedPathSize_le_four G hPath
  have hclass : HasWOWII314StructuralClassification G := by
    rcases inducedC5_or_bipartite_side G hG hTriFree hNoP5 with
      hC5 | ⟨side, hpart⟩
    · obtain ⟨x0, x1, x2, x3, x4, hC⟩ := hC5
      exact hasWOWII314StructuralClassification_of_FormsInducedC5
        G hG hTriFree hNoP5 hC
    · exact hasWOWII314StructuralClassification_of_bipartite_side
        G hG side hpart hNoP5
  exact conjecture314_of_structural_classification G hG hTriFree hPath hclass

#print axioms WrittenOnTheWallII.GraphConjecture314.conjecture314_proved

end WrittenOnTheWallII.GraphConjecture314
