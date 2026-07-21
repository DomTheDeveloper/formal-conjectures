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

namespace WrittenOnTheWallII.GraphConjecture100ForkProof

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem indepNum_induce_le (G : SimpleGraph α) (U : Set α) :
    (G.induce U).indepNum ≤ G.indepNum := by
  obtain ⟨s, hs⟩ := (G.induce U).exists_isNIndepSet_indepNum
  let e : U ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  have hs' : G.IsNIndepSet (G.induce U).indepNum (s.map e) := by
    exact (SimpleGraph.isNIndepSet_induce).mp hs
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

private theorem maximumIndepSet_card_le_compl_mul_maxLocal
    [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (S : Finset α) (hS : G.IsMaximumIndepSet S) :
    S.card ≤ Sᶜ.card *
      (Finset.univ.image (indepNeighborsCard G)).max' (by simp) := by
  let locals := Finset.univ.image (indepNeighborsCard G)
  let L := locals.max' (by simp [locals])
  have hex : ∀ s : S, ∃ t : α, G.Adj s t := by
    intro s
    obtain ⟨z, hz⟩ := exists_ne (s : α)
    exact G.degree_pos_iff_exists_adj.mp
      ((hconn.preconnected (s : α) z).degree_pos_left hz)
  choose f hf using hex
  have hfout (s : S) : f s ∉ S := by
    intro hmem
    exact (hS.isIndepSet s.property hmem (G.ne_of_adj (hf s))) (hf s)
  let fT : S → Sᶜ := fun s => ⟨f s, by simpa using hfout s⟩
  have hfiber (y : Sᶜ) :
      (Finset.univ.filter (fun x : S => fT x = y)).card ≤ L := by
    let N : Finset S := Finset.univ.filter (fun x => G.Adj (y : α) (x : α))
    have hsub :
        Finset.univ.filter (fun x : S => fT x = y) ⊆ N := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hval : f x = (y : α) := congrArg Subtype.val hx
      simpa [hval] using (hf x).symm
    have hNcard : N.card = (S.filter (G.Adj (y : α))).card := by
      let e : S ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
      have hmap : N.map e = S.filter (G.Adj (y : α)) := by
        ext x
        simp [N, e]
      rw [← hmap, Finset.card_map]
    calc
      (Finset.univ.filter (fun x : S => fT x = y)).card ≤ N.card :=
        Finset.card_le_card hsub
      _ = (S.filter (G.Adj (y : α))).card := hNcard
      _ ≤ indepNeighborsCard G (y : α) :=
        card_filter_adj_le_indepNeighborsCard G S hS.isIndepSet (y : α)
      _ ≤ L := by
        apply Finset.le_max'
        simp [locals]
  change S.card ≤ Sᶜ.card * L
  by_contra hnot
  have hlt : Fintype.card Sᶜ * L < Fintype.card S := by
    simpa using (Nat.lt_of_not_ge hnot)
  obtain ⟨y, hy⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := fT) hlt
  exact (not_lt_of_ge (hfiber y)) hy

/-- The numerical inequality used in the proof of the exact Formal Conjectures
statement of WOWII Conjecture 100. -/
theorem arithmetic_ceiling_bound
    (A L m : ℕ) (q2 : ℝ)
    (hA : 2 ≤ A) (hL : 1 ≤ L) (hLA : L ≤ A) (hAm : A ≤ m * L)
    (hq2 :
      (A : ℝ) * ((A : ℝ) - 1) ^ 2
        + (2 * (A : ℝ) - 1) * (m : ℝ) * ((A : ℝ) - (L : ℝ))
        + (m : ℝ) * ((A : ℝ) - (L : ℝ)) ^ 2 ≤ q2) :
    (A : ℝ) ≤
      ((⌈(((L : ℝ) + (1 / 2) * Real.sqrt q2) / 2)⌉ : ℤ) : ℝ) := by
  have hAr : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLAr : (L : ℝ) ≤ A := by exact_mod_cast hLA
  have hAmr : (A : ℝ) ≤ (m : ℝ) * L := by exact_mod_cast hAm
  have hdiff : 0 ≤ (A : ℝ) - L := sub_nonneg.mpr hLAr
  have htwice : 0 ≤ 2 * (A : ℝ) - 1 := by linarith
  have hq2non : 0 ≤ q2 := by
    have hmnon : 0 ≤ (m : ℝ) := by positivity
    have hbase : 0 ≤ (A : ℝ) * ((A : ℝ) - 1) ^ 2 := by positivity
    have hcross :
        0 ≤ (2 * (A : ℝ) - 1) * (m : ℝ) * ((A : ℝ) - L) := by positivity
    have hout : 0 ≤ (m : ℝ) * ((A : ℝ) - L) ^ 2 := by positivity
    linarith
  let q : ℝ := Real.sqrt q2
  have hqnon : 0 ≤ q := by simp [q]
  have hqsq : q ^ 2 = q2 := by
    simp only [q]
    exact Real.sq_sqrt hq2non
  have hstrict :
      (A : ℝ) - 1 < ((L : ℝ) + (1 / 2) * q) / 2 := by
    by_cases hsmall : A < 15
    · have hAle : A ≤ 14 := by omega
      interval_cases A <;> interval_cases L <;>
        norm_num at hA hL hLA hAmr hq2 hqsq ⊢ <;>
        nlinarith
    · have hA15 : 15 ≤ A := by omega
      have hx : 0 ≤ (A : ℝ) - 15 := by exact_mod_cast hA15
      have hbase_le :
          (A : ℝ) * ((A : ℝ) - 1) ^ 2 ≤ q2 := by
        have hmnon : 0 ≤ (m : ℝ) := by positivity
        have hcross :
            0 ≤ (2 * (A : ℝ) - 1) * (m : ℝ) * ((A : ℝ) - L) := by positivity
        have hout : 0 ≤ (m : ℝ) * ((A : ℝ) - L) ^ 2 := by positivity
        linarith
      have hpoly :
          (4 * (A : ℝ) - 6) ^ 2 < (A : ℝ) * ((A : ℝ) - 1) ^ 2 := by
        have hcub : 0 ≤ ((A : ℝ) - 15) ^ 3 := pow_nonneg hx 3
        have hsqx : 0 ≤ ((A : ℝ) - 15) ^ 2 := sq_nonneg _
        nlinarith
      have hthreshold : 0 ≤ 4 * (A : ℝ) - 6 := by linarith
      have hqgt : 4 * (A : ℝ) - 6 < q := by
        nlinarith
      nlinarith
  have hz : (A : ℤ) ≤ ⌈(((L : ℝ) + (1 / 2) * q) / 2)⌉ := by
    rw [Int.le_ceil_iff]
    norm_num
    exact hstrict
  simpa [q] using_mod_cast hz

end WrittenOnTheWallII.GraphConjecture100ForkProof
