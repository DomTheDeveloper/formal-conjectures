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
# Exact proof infrastructure for WOWII Conjecture 100

This module develops the proof of the exact theorem currently encoded in
`GraphConjecture100.lean`, whose right-hand side uses the degree `L²` norm of
the complement graph. It does not claim to prove the differently documented
diameter formulation.
-/

namespace WrittenOnTheWallII.GraphConjecture100ForkProof

open Classical SimpleGraph

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

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

private theorem one_le_maxLocalIndependence
    [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected) :
    1 ≤ (Finset.univ.image (indepNeighborsCard G)).max' (by simp) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have hdeg : 0 < G.degree a := hconn.preconnected.degree_pos_of_nontrivial a
  obtain ⟨c, hac⟩ := (G.degree_pos_iff_exists_adj (v := a)).mp hdeg
  have hsingle : G.IsIndepSet (({c} : Finset α) : Set α) := by simp
  have hlocal : 1 ≤ indepNeighborsCard G a := by
    have hcard := card_filter_adj_le_indepNeighborsCard G {c} hsingle a
    have heq : ({c} : Finset α).filter (G.Adj a) = {c} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun hx => hx.1
      · intro hxc
        subst x
        exact ⟨rfl, hac⟩
    rw [heq] at hcard
    simpa using hcard
  apply le_trans hlocal
  apply Finset.le_max'
  simp

private theorem two_le_maximumIndepSet_card
    [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hGc : Gᶜ.Connected) (S : Finset α) (hS : G.IsMaximumIndepSet S) :
    2 ≤ S.card := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have hdeg : 0 < (Gᶜ).degree a := hGc.preconnected.degree_pos_of_nontrivial a
  obtain ⟨c, hac⟩ := ((Gᶜ).degree_pos_iff_exists_adj (v := a)).mp hdeg
  have hp : G.IsIndepSet ((({a, c} : Finset α) : Set α)) := by
    rw [← SimpleGraph.isClique_compl]
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      (SimpleGraph.isClique_pair.mpr (fun _ => hac))
  have hle := hS.maximum ({a, c} : Finset α) hp
  simpa [(Gᶜ).ne_of_adj hac] using hle

private theorem maximumIndepSet_card_le_compl_mul_maxLocal
    [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (S : Finset α) (hS : G.IsMaximumIndepSet S) :
    S.card ≤ (Sᶜ).card *
      (Finset.univ.image (indepNeighborsCard G)).max' (by simp) := by
  let locals := Finset.univ.image (indepNeighborsCard G)
  let L := locals.max' (by simp [locals])
  have hex : ∀ s : S, ∃ t : α, G.Adj s t := by
    intro s
    have hdeg : 0 < G.degree (s : α) :=
      hconn.preconnected.degree_pos_of_nontrivial (s : α)
    exact (G.degree_pos_iff_exists_adj (v := (s : α))).mp hdeg
  choose f hf using hex
  have hfout (s : S) : f s ∉ S := by
    intro hmem
    exact (hS.isIndepSet s.property hmem (G.ne_of_adj (hf s))) (hf s)
  let fT : ↥S → ↥(Sᶜ) := fun s => ⟨f s, by simpa using hfout s⟩
  have hfiber (y : ↥(Sᶜ)) :
      (Finset.univ.filter (fun x : S => fT x = y)).card ≤ L := by
    let N : Finset S := Finset.univ.filter (fun x => G.Adj (y : α) (x : α))
    have hsub :
        Finset.univ.filter (fun x : S => fT x = y) ⊆ N := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
      have hval : f x = (y : α) := congrArg Subtype.val hx
      simpa [hval] using (hf x).symm
    have hNcard : N.card = (S.filter (G.Adj (y : α))).card := by
      let e : S ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
      have hmap : N.map e = S.filter (G.Adj (y : α)) := by
        ext x
        simp [N, e, and_comm]
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
  change S.card ≤ (Sᶜ).card * L
  by_contra hnot
  have hlt0 : (Sᶜ).card * L < S.card := Nat.lt_of_not_ge hnot
  have hlt : Fintype.card ↥(Sᶜ) * L < Fintype.card ↥S := by
    simpa only [Fintype.card_coe] using hlt0
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
  rw [← hqsq] at hq2
  have hstrict :
      (A : ℝ) - 1 < ((L : ℝ) + (1 / 2) * q) / 2 := by
    by_contra hnot
    have hnot' : ((L : ℝ) + (1 / 2) * q) / 2 ≤ (A : ℝ) - 1 :=
      le_of_not_gt hnot
    let T : ℝ := 4 * (A : ℝ) - 4 - 2 * (L : ℝ)
    have hTnon : 0 ≤ T := by
      dsimp [T]
      nlinarith
    have hqT : q ≤ T := by
      dsimp [T]
      nlinarith
    have hsq : q ^ 2 ≤ T ^ 2 := by
      have h1 : 0 ≤ q * (T - q) := mul_nonneg hqnon (sub_nonneg.mpr hqT)
      have h2 : 0 ≤ T * (T - q) := mul_nonneg hTnon (sub_nonneg.mpr hqT)
      nlinarith
    by_cases hEq : L = A
    · subst L
      have hbase : (A : ℝ) * ((A : ℝ) - 1) ^ 2 ≤ q ^ 2 := by
        simpa using hq2
      have hx : 0 ≤ (A : ℝ) - 2 := by nlinarith
      have hpoly : T ^ 2 < (A : ℝ) * ((A : ℝ) - 1) ^ 2 := by
        dsimp [T]
        have hx3 : 0 ≤ ((A : ℝ) - 2) ^ 3 := pow_nonneg hx 3
        nlinarith
      nlinarith
    · have hLlt : L < A := lt_of_le_of_ne hLA hEq
      by_cases hLone : L = 1
      · subst L
        have hmA : (A : ℝ) ≤ m := by simpa using hAmr
        have hA1 : 0 ≤ (A : ℝ) - 1 := by nlinarith
        have h2A1 : 0 ≤ 2 * (A : ℝ) - 1 := by nlinarith
        let C : ℝ :=
          (2 * (A : ℝ) - 1) * ((A : ℝ) - 1) + ((A : ℝ) - 1) ^ 2
        have hcoef : 0 ≤ C := by
          dsimp [C]
          exact add_nonneg (mul_nonneg h2A1 hA1) (sq_nonneg _)
        have hq2C :
            (A : ℝ) * ((A : ℝ) - 1) ^ 2 + (m : ℝ) * C ≤ q ^ 2 := by
          dsimp [C]
          nlinarith [hq2]
        have hminC :
            (A : ℝ) * ((A : ℝ) - 1) ^ 2 + (A : ℝ) * C ≤ q ^ 2 := by
          calc
            (A : ℝ) * ((A : ℝ) - 1) ^ 2 + (A : ℝ) * C
                ≤ (A : ℝ) * ((A : ℝ) - 1) ^ 2 + (m : ℝ) * C := by
                  gcongr
            _ ≤ q ^ 2 := hq2C
        have hx : 0 ≤ (A : ℝ) - 2 := by nlinarith
        have hpolyC : T ^ 2 <
            (A : ℝ) * ((A : ℝ) - 1) ^ 2 + (A : ℝ) * C := by
          dsimp [T, C]
          have hx3 : 0 ≤ ((A : ℝ) - 2) ^ 3 := pow_nonneg hx 3
          have hx2 : 0 ≤ ((A : ℝ) - 2) ^ 2 := sq_nonneg _
          nlinarith
        nlinarith
      · have hLtwo : 2 ≤ L := by omega
        have hmtwo : 2 ≤ m := by
          by_contra hm
          have hmle : m ≤ 1 := by omega
          have hm_cases : m = 0 ∨ m = 1 := by omega
          rcases hm_cases with rfl | rfl
          · norm_num at hAm
            omega
          · norm_num at hAm
            omega
        have hmtwor : (2 : ℝ) ≤ m := by exact_mod_cast hmtwo
        have hcoef :
            0 ≤ (2 * (A : ℝ) - 1) * ((A : ℝ) - L) + ((A : ℝ) - L) ^ 2 := by
          positivity
        have hmono : 0 ≤ ((m : ℝ) - 2) *
            ((2 * (A : ℝ) - 1) * ((A : ℝ) - L) + ((A : ℝ) - L) ^ 2) :=
          mul_nonneg (sub_nonneg.mpr hmtwor) hcoef
        have hmin :
            (A : ℝ) * ((A : ℝ) - 1) ^ 2
              + 2 * (2 * (A : ℝ) - 1) * ((A : ℝ) - L)
              + 2 * ((A : ℝ) - L) ^ 2 ≤ q ^ 2 := by
          nlinarith
        have hLtwoR : (2 : ℝ) ≤ L := by exact_mod_cast hLtwo
        have hp : 0 ≤ (L : ℝ) - 2 := sub_nonneg.mpr hLtwoR
        by_cases hDone : A = L + 1
        · subst A
          have hpoly : T ^ 2 <
              ((L + 1 : ℕ) : ℝ) * (((L + 1 : ℕ) : ℝ) - 1) ^ 2
                + 2 * (2 * ((L + 1 : ℕ) : ℝ) - 1) * (((L + 1 : ℕ) : ℝ) - L)
                + 2 * (((L + 1 : ℕ) : ℝ) - L) ^ 2 := by
            dsimp [T]
            have hp3 : 0 ≤ ((L : ℝ) - 2) ^ 3 := pow_nonneg hp 3
            have hp2 : 0 ≤ ((L : ℝ) - 2) ^ 2 := sq_nonneg _
            norm_num at *
            nlinarith
          nlinarith
        · by_cases hDtwo : A = L + 2
          · subst A
            have hpoly : T ^ 2 <
                ((L + 2 : ℕ) : ℝ) * (((L + 2 : ℕ) : ℝ) - 1) ^ 2
                  + 2 * (2 * ((L + 2 : ℕ) : ℝ) - 1) * (((L + 2 : ℕ) : ℝ) - L)
                  + 2 * (((L + 2 : ℕ) : ℝ) - L) ^ 2 := by
              dsimp [T]
              have hp3 : 0 ≤ ((L : ℝ) - 2) ^ 3 := pow_nonneg hp 3
              have hp2 : 0 ≤ ((L : ℝ) - 2) ^ 2 := sq_nonneg _
              norm_num at *
              nlinarith
            nlinarith
          · have hDthree : L + 3 ≤ A := by omega
            have hDthreeR : (L : ℝ) + 3 ≤ A := by exact_mod_cast hDthree
            have hd0 : 0 ≤ (A : ℝ) - L - 1 := by nlinarith
            have hd1 : 0 ≤ (A : ℝ) - L - 2 := by nlinarith
            have hd2 : 0 ≤ (A : ℝ) - L - 3 := by nlinarith
            have hprod : 0 ≤ ((A : ℝ) - L - 1) * ((A : ℝ) - L - 2) *
                ((A : ℝ) - L - 3) := by positivity
            have hpoly : T ^ 2 <
                (A : ℝ) * ((A : ℝ) - 1) ^ 2
                  + 2 * (2 * (A : ℝ) - 1) * ((A : ℝ) - L)
                  + 2 * ((A : ℝ) - L) ^ 2 := by
              dsimp [T]
              have hp3 : 0 ≤ ((L : ℝ) - 2) ^ 3 := pow_nonneg hp 3
              have hp2 : 0 ≤ ((L : ℝ) - 2) ^ 2 := sq_nonneg _
              have hmix1 : 0 ≤ ((A : ℝ) - L - 1) ^ 2 * ((L : ℝ) - 2) := by
                positivity
              have hmix2 : 0 ≤ ((A : ℝ) - L - 1) * ((L : ℝ) - 2) ^ 2 := by
                positivity
              have hmix3 : 0 ≤ ((A : ℝ) - L - 1) * ((L : ℝ) - 2) := by
                positivity
              nlinarith
            nlinarith
  have hz : (A : ℤ) ≤ ⌈(((L : ℝ) + (1 / 2) * q) / 2)⌉ := by
    rw [Int.le_ceil_iff]
    norm_num
    exact hstrict
  have hzreal : ((A : ℤ) : ℝ) ≤
      ((⌈(((L : ℝ) + (1 / 2) * q) / 2)⌉ : ℤ) : ℝ) := by
    exact_mod_cast hz
  simpa [q] using hzreal

end WrittenOnTheWallII.GraphConjecture100ForkProof
