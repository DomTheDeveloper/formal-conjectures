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
# Erdős Problem 545: literal counterexamples

The statement in Formal Conjectures issue #782 allows isolated vertices and does
not prescribe the order of the graph. This file isolates the resulting defect.

Let `singleEdgeGraph r` be one edge together with `r` isolated vertices. Its
(non-induced) two-colour Ramsey number is exactly `r + 2`, because a copy needs
`r + 2` distinct host vertices, while on exactly `r + 2` vertices the unique
edge of the pattern may be mapped to any host edge and given its colour.

Consequently:

* `K₂ ⊔ K₁` has one edge but Ramsey number `3 > 2 = R(K₂)`;
* `K₂ ⊔ 2K₁` has one edge but Ramsey number `4 > 3 = R(K₂ ⊔ K₁)`.

These disprove the two claims literally as written; they do not rule out a
corrected statement forbidding isolated vertices or bounding the graph order.
-/

namespace Erdos545Counterexample

/-- One edge, between vertices `0` and `1`, together with `r` isolated vertices. -/
def singleEdgeGraph (r : ℕ) : SimpleGraph (Fin (r + 2)) where
  Adj u v := (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)
  symm := by
    intro u v h
    rcases h with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩
  loopless := by
    intro v h
    rcases h with h | h <;> omega

/-- The graph really has exactly the single undirected edge `{0, 1}`. -/
theorem singleEdgeGraph_adj_iff (r : ℕ) (u v : Fin (r + 2)) :
    (singleEdgeGraph r).Adj u v ↔
      (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) :=
  Iff.rfl

/-- A non-induced monochromatic copy of a finite simple graph in a two-coloured complete graph. -/
def HasMonochromaticCopy {k m : ℕ} (G : SimpleGraph (Fin k))
    (c : Finset (Fin m) → Bool) : Prop :=
  ∃ f : Fin k ↪ Fin m, ∃ color : Bool,
    ∀ ⦃u v : Fin k⦄, G.Adj u v → c {f u, f v} = color

/-- Every two-colouring on `m` host vertices contains a monochromatic copy of `G`. -/
def IsRamseyAt {k : ℕ} (G : SimpleGraph (Fin k)) (m : ℕ) : Prop :=
  ∀ c : Finset (Fin m) → Bool, HasMonochromaticCopy G c

/-- The Ramsey number of one edge together with `r` isolated vertices. -/
noncomputable def singleEdgeRamseyNumber (r : ℕ) : ℕ :=
  sInf {m : ℕ | IsRamseyAt (singleEdgeGraph r) m}

lemma singleEdge_ramsey_at_order (r : ℕ) :
    IsRamseyAt (singleEdgeGraph r) (r + 2) := by
  intro c
  refine ⟨Function.Embedding.refl _, c {0, 1}, ?_⟩
  intro u v huv
  rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · simp [Finset.pair_comm]

lemma order_le_of_singleEdge_ramsey_at (r m : ℕ)
    (h : IsRamseyAt (singleEdgeGraph r) m) : r + 2 ≤ m := by
  obtain ⟨f, _, _⟩ := h (fun _ => false)
  have hcard := Fintype.card_le_of_injective f f.injective
  simpa using hcard

/-- `R(K₂ ⊔ rK₁) = r + 2`. -/
theorem singleEdgeRamseyNumber_eq (r : ℕ) :
    singleEdgeRamseyNumber r = r + 2 := by
  apply le_antisymm
  · exact Nat.sInf_le (singleEdge_ramsey_at_order r)
  · apply le_csInf
    · exact ⟨r + 2, singleEdge_ramsey_at_order r⟩
    · intro m hm
      exact order_le_of_singleEdge_ramsey_at r m hm

/-- Counterexample to the first claim: `K₂ ⊔ K₁` has larger Ramsey number than `K₂`. -/
theorem first_claim_counterexample :
    singleEdgeRamseyNumber 1 > singleEdgeRamseyNumber 0 := by
  rw [singleEdgeRamseyNumber_eq, singleEdgeRamseyNumber_eq]
  norm_num

/-- Counterexample to the generalized `t = 0` claim. -/
theorem generalized_claim_counterexample :
    singleEdgeRamseyNumber 2 > singleEdgeRamseyNumber 1 := by
  rw [singleEdgeRamseyNumber_eq, singleEdgeRamseyNumber_eq]
  norm_num

#print axioms singleEdgeRamseyNumber_eq
#print axioms first_claim_counterexample
#print axioms generalized_claim_counterexample

end Erdos545Counterexample
