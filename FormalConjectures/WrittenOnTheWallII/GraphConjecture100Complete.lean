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

import FormalConjectures.WrittenOnTheWallII.GraphConjecture100ForkProof
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Complete proof of the source-aligned Formal Conjectures statement of WOWII 100

The encoded invariant `degreeL2Norm Gᶜ` is the square root of the sum of the
squares of the complement degrees, matching the WOWII definition of graph
length. No connectedness assumption on the complement is needed.
-/

namespace WrittenOnTheWallII.GraphConjecture100Complete

open Classical SimpleGraph

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem indepNum_induce_le (G : SimpleGraph α) (U : Set α) :
    (G.induce U).indepNum ≤ G.indepNum := by
  obtain ⟨s, hs⟩ := (G.induce U).exists_isNIndepSet_indepNum
  let e : U ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  have hs' : G.IsNIndepSet (G.induce U).indepNum (s.map e) := by
    refine ⟨?_, by simpa [Finset.card_map] using hs.card_eq⟩
    rintro x hx y hy hxy hadj
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    apply hs.isIndepSet hx' hy'
    · intro h
      apply hxy
      exact congrArg Subtype.val h
    · exact hadj
  have hcard := hs'.isIndepSet.card_le_indepNum
  simpa [Finset.card_map, hs.card_eq] using hcard

private theorem card_filter_adj_le_indepNeighborsCard
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (S : Finset α) (hS : G.IsIndepSet (S : Set α)) (v : α) :
    (S.filter (G.Adj v)).card ≤ indepNeighborsCard G v := by
  let U : Finset (G.neighborSet v) :=
    Finset.univ.filter (fun x => (x : α) ∈ S)
  have hU : (G.induce (G.neighborSet v)).IsIndepSet (U : Set _) := by
    rintro x hx y hy hxy hxyAdj
    apply hS
    · simpa [U] using hx
    · simpa [U] using hy
    · exact fun h => hxy (Subtype.ext h)
    · exact hxyAdj
  let e : G.neighborSet v ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : U.map e = S.filter (G.Adj v) := by
    ext x
    simp [U, e]
  rw [← hmap, Finset.card_map]
  exact hU.card_le_indepNum

private theorem maxLocalIndependence_le_indepNum [Nonempty α] (G : SimpleGraph α) :
    (Finset.univ.image (indepNeighborsCard G)).max' (by simp) ≤ G.indepNum := by
  apply Finset.max'_le
  intro n hn
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hn
  exact indepNum_induce_le G (G.neighborSet v)

private theorem arithmetic_ceiling_bound_pos
    (A L m : ℕ) (q2 : ℝ)
    (hA : 1 ≤ A) (hL : 1 ≤ L) (hLA : L ≤ A) (hAm : A ≤ m * L)
    (hq2 :
      (A : ℝ) * ((A : ℝ) - 1) ^ 2
        + (2 * (A : ℝ) - 1) * (m : ℝ) * ((A : ℝ) - (L : ℝ))
        + (m : ℝ) * ((A : ℝ) - (L : ℝ)) ^ 2 ≤ q2) :
    (A : ℝ) ≤
      ((⌈(((L : ℝ) + (1 / 2) * Real.sqrt q2) / 2)⌉ : ℤ) : ℝ) := by
  by_cases hAone : A = 1
  · have hLone : L = 1 := by omega
    subst A
    subst L
    have hq2non : 0 ≤ q2 := by
      norm_num at hq2
      exact hq2
    have hqnon : 0 ≤ Real.sqrt q2 := Real.sqrt_nonneg _
    have hxpos :
        0 < (1 : ℝ) + (1 / 2) * Real.sqrt q2 := by
      nlinarith
    have hz :
        (1 : ℤ) ≤ ⌈(((1 : ℝ) + (1 / 2) * Real.sqrt q2) / 2)⌉ := by
      rw [Int.le_ceil_iff]
      norm_num
      exact hxpos
    have hzreal :
        ((1 : ℤ) : ℝ) ≤
          ((⌈(((1 : ℝ) + (1 / 2) * Real.sqrt q2) / 2)⌉ : ℤ) : ℝ) := by
      exact_mod_cast hz
    simpa using hzreal
  · exact GraphConjecture100ForkProof.arithmetic_ceiling_bound
      A L m q2 (by omega) hL hLA hAm hq2

/-- The exact source-aligned `degreeL2Norm` theorem encoded as WOWII Conjecture 100. -/
theorem conjecture100
    [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤
      ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
  dsimp
  obtain ⟨S, hS⟩ := G.maximumIndepSet_exists
  let H : SimpleGraph α := Gᶜ
  let T : Finset α := Sᶜ
  let A : ℕ := S.card
  let L : ℕ := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
  let D : ℕ := A - L
  let r : α → ℕ := fun s => (T.bipartiteAbove H.Adj s).card
  let c : α → ℕ := fun t => (S.bipartiteBelow H.Adj t).card
  have hAeq : A = G.indepNum := by
    exact G.maximumIndepSet_card_eq_indepNum S hS
  have hApos : 1 ≤ A := by
    let v : α := Classical.choice (inferInstance : Nonempty α)
    have hv : G.IsIndepSet ((({v} : Finset α) : Set α)) := by simp
    have hle := hS.maximum ({v} : Finset α) hv
    simpa [A] using hle
  have hLA : L ≤ A := by
    rw [hAeq]
    exact maxLocalIndependence_le_indepNum G
  have hGlocal (t : α) : (S.filter (G.Adj t)).card ≤ L := by
    apply le_trans (card_filter_adj_le_indepNeighborsCard G S hS.isIndepSet t)
    change indepNeighborsCard G t ≤
      (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    apply Finset.le_max'
    simp
  have hGabove : ∀ s ∈ S, 1 ≤ (T.bipartiteAbove G.Adj s).card := by
    intro s hs
    have hdeg : 0 < G.degree s := h.preconnected.degree_pos_of_nontrivial s
    obtain ⟨t, hst⟩ := (G.degree_pos_iff_exists_adj (v := s)).mp hdeg
    have ht : t ∈ T := by
      simp only [T, Finset.mem_compl]
      intro htS
      exact (hS.isIndepSet hs htS (G.ne_of_adj hst)) hst
    exact Finset.card_pos.mpr ⟨t, by simp [Finset.bipartiteAbove, ht, hst]⟩
  have hGbelow : ∀ t ∈ T, (S.bipartiteBelow G.Adj t).card ≤ L := by
    intro t ht
    have heq : S.bipartiteBelow G.Adj t = S.filter (G.Adj t) := by
      ext s
      simp [Finset.bipartiteBelow, G.adj_comm]
    rw [heq]
    exact hGlocal t
  have hAm : A ≤ T.card * L := by
    have hdc := Finset.card_mul_le_card_mul (r := G.Adj) (s := S) (t := T)
      (m := 1) (n := L) hGabove hGbelow
    simpa [A] using hdc
  have hL : 1 ≤ L := by
    by_contra hnot
    have hzero : L = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hAm
    simp at hAm
    omega
  have hCeq (t : α) (ht : t ∈ T) :
      S.bipartiteBelow H.Adj t = S.filter (fun s => ¬G.Adj t s) := by
    ext s
    have htS : t ∉ S := by simpa [T] using ht
    by_cases hs : s ∈ S
    · have hne : t ≠ s := fun hts => htS (hts ▸ hs)
      simp [Finset.bipartiteBelow, H, hs, hne.symm, G.adj_comm]
    · simp [Finset.bipartiteBelow, hs]
  have hCpart (t : α) (ht : t ∈ T) :
      (S.filter (G.Adj t)).card + c t = A := by
    change (S.filter (G.Adj t)).card +
      (S.bipartiteBelow H.Adj t).card = A
    rw [hCeq t ht]
    let P := S.filter (G.Adj t)
    let Q := S.filter (fun s => ¬G.Adj t s)
    have hdisj : Disjoint P Q := by
      rw [Finset.disjoint_left]
      intro x hxP hxQ
      simp [P, Q] at hxP hxQ
      exact hxQ.2 hxP.2
    have hunion : P ∪ Q = S := by
      ext x
      by_cases hx : x ∈ S
      · by_cases hadj : G.Adj t x <;> simp [P, Q, hx, hadj]
      · simp [P, Q, hx]
    calc
      (S.filter (G.Adj t)).card + (S.filter (fun s => ¬G.Adj t s)).card
          = P.card + Q.card := rfl
      _ = (P ∪ Q).card := (Finset.card_union_of_disjoint hdisj).symm
      _ = S.card := by rw [hunion]
      _ = A := rfl
  have hC_lower : ∀ t ∈ T, D ≤ c t := by
    intro t ht
    have hk := hGlocal t
    have hp := hCpart t ht
    dsimp [D]
    omega
  have hC_degree : ∀ t ∈ T, c t ≤ H.degree t := by
    intro t ht
    change (S.bipartiteBelow H.Adj t).card ≤ H.degree t
    rw [hCeq t ht]
    apply Finset.card_le_card
    intro s hs
    rcases Finset.mem_filter.mp hs with ⟨hsS, hnot⟩
    have htS : t ∉ S := by simpa [T] using ht
    have hne : t ≠ s := fun hts => htS (hts ▸ hsS)
    simp only [SimpleGraph.mem_neighborFinset]
    simp [H, hne, hnot]
  have hdouble : (∑ s ∈ S, r s) = ∑ t ∈ T, c t := by
    simpa [r, c] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := H.Adj) (s := S) (t := T))
  have hcross : T.card * D ≤ ∑ s ∈ S, r s := by
    calc
      T.card * D = ∑ t ∈ T, D := by simp
      _ ≤ ∑ t ∈ T, c t := Finset.sum_le_sum fun t ht => hC_lower t ht
      _ = ∑ s ∈ S, r s := hdouble.symm
  have hR_degree : ∀ s ∈ S, A - 1 + r s ≤ H.degree s := by
    intro s hs
    let P := S.erase s
    let Q := T.bipartiteAbove H.Adj s
    have hPsub : P ⊆ H.neighborFinset s := by
      intro x hx
      have hxS : x ∈ S := (Finset.mem_erase.mp hx).2
      have hxs : x ≠ s := (Finset.mem_erase.mp hx).1
      have hnot : ¬G.Adj s x := fun hadj =>
        (hS.isIndepSet hs hxS (G.ne_of_adj hadj)) hadj
      simp only [SimpleGraph.mem_neighborFinset]
      simp [H, hxs.symm, hnot]
    have hQsub : Q ⊆ H.neighborFinset s := by
      intro x hx
      simp [Q, Finset.bipartiteAbove] at hx
      simpa [SimpleGraph.mem_neighborFinset] using hx.2
    have hdisj : Disjoint P Q := by
      rw [Finset.disjoint_left]
      intro x hxP hxQ
      have hxS : x ∈ S := (Finset.mem_erase.mp hxP).2
      have hxQ' : x ∈ T ∧ H.Adj s x := by
        simpa [Q, Finset.bipartiteAbove] using hxQ
      have hxT : x ∈ T := hxQ'.1
      have hxNotS : x ∉ S := by simpa [T] using hxT
      exact hxNotS hxS
    have hsub : P ∪ Q ⊆ H.neighborFinset s := Finset.union_subset hPsub hQsub
    have hcard := Finset.card_le_card hsub
    have hscard : P.card = A - 1 := by
      simp [P, A, hs]
    have hqcard : Q.card = r s := rfl
    rw [Finset.card_union_of_disjoint hdisj, hscard, hqcard] at hcard
    exact hcard
  have hSpoint : ∀ s ∈ S,
      (A - 1) ^ 2 + (2 * A - 1) * r s ≤ (H.degree s) ^ 2 := by
    intro s hs
    have hd := hR_degree s hs
    have hcoeff : 2 * A - 1 = 2 * (A - 1) + 1 := by omega
    have hrsq : r s ≤ (r s) ^ 2 := by nlinarith [Nat.zero_le (r s)]
    have hpow : (A - 1 + r s) ^ 2 ≤ (H.degree s) ^ 2 := by gcongr
    rw [hcoeff]
    nlinarith
  have hSpointSum :
      (∑ s ∈ S, ((A - 1) ^ 2 + (2 * A - 1) * r s)) ≤
        ∑ s ∈ S, (H.degree s) ^ 2 :=
    Finset.sum_le_sum fun s hs => hSpoint s hs
  have hSexpand :
      (∑ s ∈ S, ((A - 1) ^ 2 + (2 * A - 1) * r s)) =
        A * (A - 1) ^ 2 + (2 * A - 1) * (∑ s ∈ S, r s) := by
    simp [Finset.sum_add_distrib, A, Finset.mul_sum, Nat.mul_comm]
  rw [hSexpand] at hSpointSum
  have hcrossMul :
      (2 * A - 1) * (T.card * D) ≤ (2 * A - 1) * (∑ s ∈ S, r s) :=
    Nat.mul_le_mul_left _ hcross
  have hSsum :
      A * (A - 1) ^ 2 + (2 * A - 1) * (T.card * D) ≤
        ∑ s ∈ S, (H.degree s) ^ 2 := by
    omega
  have hTpoint : ∀ t ∈ T, D ^ 2 ≤ (H.degree t) ^ 2 := by
    intro t ht
    have hd : D ≤ H.degree t := (hC_lower t ht).trans (hC_degree t ht)
    gcongr
  have hTsum : T.card * D ^ 2 ≤ ∑ t ∈ T, (H.degree t) ^ 2 := by
    calc
      T.card * D ^ 2 = ∑ t ∈ T, D ^ 2 := by simp
      _ ≤ ∑ t ∈ T, (H.degree t) ^ 2 := Finset.sum_le_sum fun t ht => hTpoint t ht
  have hpartition :
      (∑ s ∈ S, (H.degree s) ^ 2) + (∑ t ∈ T, (H.degree t) ^ 2) =
        ∑ v, (H.degree v) ^ 2 := by
    have hdisj : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro x hxS hxT
      have hxNotS : x ∉ S := by simpa [T] using hxT
      exact hxNotS hxS
    calc
      (∑ s ∈ S, (H.degree s) ^ 2) + (∑ t ∈ T, (H.degree t) ^ 2)
          = ∑ v ∈ S ∪ T, (H.degree v) ^ 2 := (Finset.sum_union hdisj).symm
      _ = ∑ v ∈ Finset.univ, (H.degree v) ^ 2 := by simp [T]
      _ = ∑ v, (H.degree v) ^ 2 := rfl
  have hNat :
      A * (A - 1) ^ 2 + (2 * A - 1) * (T.card * D) + T.card * D ^ 2 ≤
        ∑ v, (H.degree v) ^ 2 := by
    calc
      A * (A - 1) ^ 2 + (2 * A - 1) * (T.card * D) + T.card * D ^ 2
          ≤ (∑ s ∈ S, (H.degree s) ^ 2) + (∑ t ∈ T, (H.degree t) ^ 2) :=
            Nat.add_le_add hSsum hTsum
      _ = ∑ v, (H.degree v) ^ 2 := hpartition
  have hAcast : ((A - 1 : ℕ) : ℝ) = (A : ℝ) - 1 := by
    rw [Nat.cast_sub hApos]
    norm_num
  have hCoeffCast : ((2 * A - 1 : ℕ) : ℝ) = 2 * (A : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * A)]
    norm_num
  have hDcast : (D : ℝ) = (A : ℝ) - (L : ℝ) := by
    dsimp [D]
    rw [Nat.cast_sub hLA]
  have hRealNat :
      (A : ℝ) * (((A - 1 : ℕ) : ℝ)) ^ 2
        + (((2 * A - 1 : ℕ) : ℝ)) * ((T.card : ℝ) * (D : ℝ))
        + (T.card : ℝ) * (D : ℝ) ^ 2 ≤
          ∑ v, ((H.degree v : ℝ) ^ 2) := by
    exact_mod_cast hNat
  have hReal :
      (A : ℝ) * ((A : ℝ) - 1) ^ 2
        + (2 * (A : ℝ) - 1) * (T.card : ℝ) * ((A : ℝ) - (L : ℝ))
        + (T.card : ℝ) * ((A : ℝ) - (L : ℝ)) ^ 2 ≤
          ∑ v, ((H.degree v : ℝ) ^ 2) := by
    simpa [hAcast, hCoeffCast, hDcast, mul_assoc] using hRealNat
  have harith :=
    arithmetic_ceiling_bound_pos
      A L T.card (∑ v, ((H.degree v : ℝ) ^ 2)) hApos hL hLA hAm hReal
  simpa [A, L, H, degreeL2Norm, hAeq] using harith

end WrittenOnTheWallII.GraphConjecture100Complete
