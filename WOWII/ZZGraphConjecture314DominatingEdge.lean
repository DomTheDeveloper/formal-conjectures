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

import WOWII.ZZGraphConjecture314Core

/-!
The bipartite dominating-edge family in the proof of WOWII Graph Conjecture 314.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

private lemma bool_eq_of_ne_same {a b s : Bool} (ha : a ≠ s) (hb : b ≠ s) : a = b := by
  cases a <;> cases b <;> cases s <;> simp_all

private lemma bool_eq_false_of_true_ne {a : Bool} (h : true ≠ a) : a = false := by
  cases a <;> simp_all

private lemma bool_eq_true_of_false_ne {a : Bool} (h : false ≠ a) : a = true := by
  cases a <;> simp_all

/-- Five ordered vertices form an induced path on five vertices. -/
def FormsInducedP5 (G : SimpleGraph α) (x0 x1 x2 x3 x4 : α) : Prop :=
  x0 ≠ x1 ∧ x0 ≠ x2 ∧ x0 ≠ x3 ∧ x0 ≠ x4 ∧
  x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧
  x2 ≠ x3 ∧ x2 ≠ x4 ∧ x3 ≠ x4 ∧
  G.Adj x0 x1 ∧ G.Adj x1 x2 ∧ G.Adj x2 x3 ∧ G.Adj x3 x4 ∧
  ¬G.Adj x0 x2 ∧ ¬G.Adj x0 x3 ∧ ¬G.Adj x0 x4 ∧
  ¬G.Adj x1 x3 ∧ ¬G.Adj x1 x4 ∧ ¬G.Adj x2 x4

/-- In a bipartite graph with a dominating edge, every minimal total dominating
set has exactly two vertices, provided the graph is induced-P5-free. -/
lemma minimalTDS_card_eq_two_of_bipartite_dominating_edge
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (side : α → Bool) (u v : α)
    (hu : side u = false) (hv : side v = true)
    (hpart : ∀ x y : α, G.Adj x y → side x ≠ side y)
    (huDom : ∀ x : α, side x = true → G.Adj u x)
    (hvDom : ∀ x : α, side x = false → G.Adj v x)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4)
    {S : Finset α} (hS : IsMinimalTotalDominatingSet G S) :
    S.card = 2 := by
  have hatMost : ∀ (s : Bool) (c : α), side c ≠ s →
      (∀ x : α, side x = s → G.Adj c x) →
      ∀ a₁ ∈ S, ∀ a₂ ∈ S, side a₁ = s → side a₂ = s → a₁ = a₂ := by
    intro s c hcSide hcDom a₁ ha₁S a₂ ha₂S ha₁side ha₂side
    by_contra ha12
    obtain ⟨b₁, hb₁a₁, hb₁priv⟩ :=
      exists_private_neighbor_of_mem_minimalTDS G hS ha₁S
    obtain ⟨b₂, hb₂a₂, hb₂priv⟩ :=
      exists_private_neighbor_of_mem_minimalTDS G hS ha₂S
    have hb₁side_ne : side b₁ ≠ s := by
      intro h
      exact hpart b₁ a₁ hb₁a₁ (h.trans ha₁side.symm)
    have hb₂side_ne : side b₂ ≠ s := by
      intro h
      exact hpart b₂ a₂ hb₂a₂ (h.trans ha₂side.symm)
    have hbside : side b₁ = side b₂ := bool_eq_of_ne_same hb₁side_ne hb₂side_ne
    have hb₁cSide : side b₁ = side c := bool_eq_of_ne_same hb₁side_ne hcSide
    have hb₂cSide : side b₂ = side c := bool_eq_of_ne_same hb₂side_ne hcSide
    have hb12 : b₁ ≠ b₂ := by
      intro h
      subst b₂
      have hEq := hb₁priv a₂ ha₂S hb₂a₂
      exact ha12 hEq.symm
    have hb₁c : b₁ ≠ c := by
      intro h
      subst b₁
      have hcA₂ : G.Adj c a₂ := hcDom a₂ ha₂side
      have hEq := hb₁priv a₂ ha₂S hcA₂
      exact ha12 hEq.symm
    have hb₂c : b₂ ≠ c := by
      intro h
      subst b₂
      have hcA₁ : G.Adj c a₁ := hcDom a₁ ha₁side
      have hEq := hb₂priv a₁ ha₁S hcA₁
      exact ha12 hEq
    have hb₁a₂ : b₁ ≠ a₂ := by
      intro h
      subst b₁
      exact hb₁side_ne ha₂side
    have hb₂a₁ : b₂ ≠ a₁ := by
      intro h
      subst b₂
      exact hb₂side_ne ha₁side
    have hcA₁ : G.Adj c a₁ := hcDom a₁ ha₁side
    have hcA₂ : G.Adj c a₂ := hcDom a₂ ha₂side
    have hn_b₁_c : ¬G.Adj b₁ c := fun h => hpart b₁ c h hb₁cSide
    have hn_b₂_c : ¬G.Adj b₂ c := fun h => hpart b₂ c h hb₂cSide
    have hn_b₁_b₂ : ¬G.Adj b₁ b₂ := fun h => hpart b₁ b₂ h hbside
    have hn_a₁_a₂ : ¬G.Adj a₁ a₂ :=
      fun h => hpart a₁ a₂ h (ha₁side.trans ha₂side.symm)
    have hn_b₁_a₂ : ¬G.Adj b₁ a₂ := by
      intro h
      exact ha12 (hb₁priv a₂ ha₂S h).symm
    have hn_b₂_a₁ : ¬G.Adj b₂ a₁ := by
      intro h
      exact ha12 (hb₂priv a₁ ha₁S h)
    have hn_a₁_b₂ : ¬G.Adj a₁ b₂ := fun h => hn_b₂_a₁ h.symm
    have hn_c_b₂ : ¬G.Adj c b₂ := fun h => hn_b₂_c h.symm
    apply hNoP5 b₁ a₁ c a₂ b₂
    unfold FormsInducedP5
    exact ⟨hb₁a₁.ne, hb₁c, hb₁a₂, hb12,
      hcA₁.ne.symm, ha12, hb₂a₁.symm,
      hcA₂.ne, hb₂c.symm, hb₂a₂.ne.symm,
      hb₁a₁, hcA₁.symm, hcA₂, hb₂a₂.symm,
      hn_b₁_c, hn_b₁_a₂, hn_b₁_b₂,
      hn_a₁_a₂, hn_a₁_b₂, hn_c_b₂⟩
  obtain ⟨a, haS, hva⟩ := hS.1 v
  have haSide : side a = false := by
    apply bool_eq_false_of_true_ne
    simpa [hv] using hpart v a hva
  obtain ⟨b, hbS, hub⟩ := hS.1 u
  have hbSide : side b = true := by
    apply bool_eq_true_of_false_ne
    simpa [hu] using hpart u b hub
  have hab : a ≠ b := by
    intro h
    subst b
    rw [haSide] at hbSide
    contradiction
  have hforall : ∀ w ∈ S, w = a ∨ w = b := by
    intro w hwS
    cases hsw : side w with
    | false =>
        left
        exact hatMost false v (by simp [hv]) hvDom w hwS a haS hsw haSide
    | true =>
        right
        exact hatMost true u (by simp [hu]) huDom w hwS b hbS hsw hbSide
  have hSeq : S = {a, b} := by
    ext w
    constructor
    · intro hw
      rcases hforall w hw with rfl | rfl <;> simp
    · intro hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact haS
      · exact hbS
  rw [hSeq]
  simp [hab]

/-- Consequently, the bipartite dominating-edge family is well totally dominated. -/
lemma isWellTotallyDominated_of_bipartite_dominating_edge
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (side : α → Bool) (u v : α)
    (hu : side u = false) (hv : side v = true)
    (hpart : ∀ x y : α, G.Adj x y → side x ≠ side y)
    (huDom : ∀ x : α, side x = true → G.Adj u x)
    (hvDom : ∀ x : α, side x = false → G.Adj v x)
    (hNoP5 : ∀ x0 x1 x2 x3 x4 : α, ¬FormsInducedP5 G x0 x1 x2 x3 x4) :
    IsWellTotallyDominated G := by
  intro S T hS hT
  rw [minimalTDS_card_eq_two_of_bipartite_dominating_edge G side u v hu hv hpart huDom hvDom hNoP5 hS,
    minimalTDS_card_eq_two_of_bipartite_dominating_edge G side u v hu hv hpart huDom hvDom hNoP5 hT]

end WrittenOnTheWallII.GraphConjecture314
