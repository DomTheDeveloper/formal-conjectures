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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 160

Audit copy. Contains two explicit proof holes.
-/

namespace WrittenOnTheWallII.GraphConjecture160

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

noncomputable def maxTrianglesAtVertex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.image (numTrianglesAtVertex G)).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

def HasC4 (G : SimpleGraph α) : Prop :=
  ∃ v : α, ∃ c : G.Walk v v, c.IsCycle ∧ c.length = 4

noncomputable def maxLocalIndependence (G : SimpleGraph α) : ℕ :=
  (Finset.univ.image (indepNeighborsCard G)).max' (by simp)

noncomputable def leafCount {G : SimpleGraph α} [DecidableRel G.Adj]
    (T : G.Subgraph) : ℕ :=
  (T.verts.toFinset.filter fun v => T.degree v = 1).card

lemma leafCount_le_Ls (G : SimpleGraph α) [DecidableRel G.Adj]
    (T : G.Subgraph) (hTspan : T.IsSpanning) (hTtree : IsTree T.coe) :
    (leafCount T : ℝ) ≤ Ls G := by
  unfold leafCount Ls
  apply le_csSup
  · refine ⟨(Fintype.card α : ℝ), ?_⟩
    rintro x ⟨S, _hS, rfl⟩
    exact_mod_cast
      (Finset.card_le_univ (S.verts.toFinset.filter fun v => S.degree v = 1))
  · exact ⟨T, ⟨hTspan, hTtree⟩, rfl⟩

/-- Extend a maximum independent neighbourhood star to a spanning tree. -/
lemma maxLocalIndependence_leafWitness (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) :
    ∃ T : G.Subgraph,
      T.IsSpanning ∧ IsTree T.coe ∧ maxLocalIndependence G ≤ leafCount T := by
  sorry

/-- Construct the stronger spanning-tree witness in the C4-free case. -/
lemma c4Free_leafWitness (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hC4 : ¬HasC4 G) :
    ∃ T : G.Subgraph,
      T.IsSpanning ∧ IsTree T.coe ∧
        maxLocalIndependence G + maxTrianglesAtVertex G ≤ leafCount T := by
  sorry

lemma maxLocalIndependence_le_Ls (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) :
    (maxLocalIndependence G : ℝ) ≤ Ls G := by
  obtain ⟨T, hTspan, hTtree, hcount⟩ := maxLocalIndependence_leafWitness G hG
  calc
    (maxLocalIndependence G : ℝ) ≤ (leafCount T : ℝ) := by
      exact_mod_cast hcount
    _ ≤ Ls G := leafCount_le_Ls G T hTspan hTtree

lemma c4Free_bound (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (hC4 : ¬HasC4 G) :
    (maxLocalIndependence G : ℝ) + (maxTrianglesAtVertex G : ℝ) ≤ Ls G := by
  obtain ⟨T, hTspan, hTtree, hcount⟩ := c4Free_leafWitness G hG hC4
  calc
    (maxLocalIndependence G : ℝ) + (maxTrianglesAtVertex G : ℝ) =
        ((maxLocalIndependence G + maxTrianglesAtVertex G : ℕ) : ℝ) := by
      norm_num
    _ ≤ (leafCount T : ℝ) := by
      exact_mod_cast hcount
    _ ≤ Ls G := leafCount_le_Ls G T hTspan hTtree

@[category research open, AMS 5]
theorem conjecture160 (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    let maxT := maxTrianglesAtVertex G
    let cC4 : ℕ := if HasC4 G then 0 else 1
    (maxL : ℝ) + (maxT : ℝ) * (cC4 : ℝ) ≤ Ls G := by
  dsimp only
  by_cases hC4 : HasC4 G
  · simpa [hC4, maxLocalIndependence] using maxLocalIndependence_le_Ls G hG
  · simpa [hC4, maxLocalIndependence] using c4Free_bound G hG hC4

#print axioms conjecture160

end WrittenOnTheWallII.GraphConjecture160
