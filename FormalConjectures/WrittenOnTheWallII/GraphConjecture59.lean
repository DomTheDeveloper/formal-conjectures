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
# Written on the Wall II - Conjecture 59

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Counterexample

The conjecture is false.  Let `H` be the bipartite graph with parts
`{0,1,2,3,4}` and `{5,6,7,8,9}` and edge set

```
05 08 09
15 16 17 18
25 26 29
35 36 37 38 39
45 46 47 49.
```

Add a universal vertex `10` and seven leaves `11,...,17`, all adjacent only to
`10`.  The resulting connected graph `G` satisfies

* `residue G = 10`;
* `b G >= 17`, since deleting vertex `10` leaves a bipartite graph;
* `largestInducedForestSize G <= 13`.

Consequently

`ceil (sqrt (residue G * b G)) >= ceil (sqrt 170) = 14 > 13`.
-/

namespace WrittenOnTheWallII.GraphConjecture59

open Classical SimpleGraph Finset

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

/-- The 18-vertex counterexample described in the module docstring. -/
private def counterG : SimpleGraph (Fin 18) where
  Adj u v :=
    u ≠ v ∧
      (u.val = 10 ∨ v.val = 10 ∨
        (u.val = 0 ∧ (v.val = 5 ∨ v.val = 8 ∨ v.val = 9)) ∨
        (v.val = 0 ∧ (u.val = 5 ∨ u.val = 8 ∨ u.val = 9)) ∨
        (u.val = 1 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 7 ∨ v.val = 8)) ∨
        (v.val = 1 ∧ (u.val = 5 ∨ u.val = 6 ∨ u.val = 7 ∨ u.val = 8)) ∨
        (u.val = 2 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 9)) ∨
        (v.val = 2 ∧ (u.val = 5 ∨ u.val = 6 ∨ u.val = 9)) ∨
        (u.val = 3 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 7 ∨ v.val = 8 ∨ v.val = 9)) ∨
        (v.val = 3 ∧ (u.val = 5 ∨ u.val = 6 ∨ u.val = 7 ∨ u.val = 8 ∨ u.val = 9)) ∨
        (u.val = 4 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 7 ∨ v.val = 9)) ∨
        (v.val = 4 ∧ (u.val = 5 ∨ u.val = 6 ∨ u.val = 7 ∨ u.val = 9)))
  symm u v h := by
    obtain ⟨hne, hcases⟩ := h
    exact ⟨hne.symm, by tauto⟩
  loopless u h := h.1 rfl

private instance counterG_decidable : DecidableRel counterG.Adj := fun u v => by
  unfold counterG
  infer_instance

private lemma counterG_adj (u v : Fin 18) : counterG.Adj u v ↔
    u ≠ v ∧
      (u.val = 10 ∨ v.val = 10 ∨
        (u.val = 0 ∧ (v.val = 5 ∨ v.val = 8 ∨ v.val = 9)) ∨
        (v.val = 0 ∧ (u.val = 5 ∨ u.val = 8 ∨ u.val = 9)) ∨
        (u.val = 1 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 7 ∨ v.val = 8)) ∨
        (v.val = 1 ∧ (u.val = 5 ∨ u.val = 6 ∨ u.val = 7 ∨ u.val = 8)) ∨
        (u.val = 2 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 9)) ∨
        (v.val = 2 ∧ (u.val = 5 ∨ u.val = 6 ∨ u.val = 9)) ∨
        (u.val = 3 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 7 ∨ v.val = 8 ∨ v.val = 9)) ∨
        (v.val = 3 ∧ (u.val = 5 ∨ u.val = 6 ∨ u.val = 7 ∨ u.val = 8 ∨ u.val = 9)) ∨
        (u.val = 4 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 7 ∨ v.val = 9)) ∨
        (v.val = 4 ∧ (u.val = 5 ∨ u.val = 6 ∨ u.val = 7 ∨ u.val = 9))) := Iff.rfl

/-- Every vertex is reachable from the universal vertex `10`. -/
private lemma counterG_reachable_from_hub (v : Fin 18) : counterG.Reachable 10 v := by
  by_cases hv : v = 10
  · subst v
    exact Reachable.refl _
  · have h10v : counterG.Adj 10 v := by
      rw [counterG_adj]
      exact ⟨hv.symm, Or.inl rfl⟩
    exact h10v.reachable

private lemma counterG_connected : counterG.Connected := by
  constructor
  intro u v
  exact (counterG_reachable_from_hub u).symm.trans (counterG_reachable_from_hub v)

/-- The Havel--Hakimi residue is exactly 10. -/
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private lemma counterG_residue : residue counterG = 10 := by
  unfold residue
  decide +kernel

private def counterColor (v : Fin 18) : Fin 2 := if v.val < 5 then 0 else 1

private lemma counterColor_valid :
    ∀ u v : Fin 18, u ≠ 10 → v ≠ 10 → counterG.Adj u v →
      counterColor u ≠ counterColor v := by
  decide

/-- Deleting the hub leaves a bipartite induced subgraph on 17 vertices. -/
private lemma counterG_b_ge : (17 : ℝ) ≤ b counterG := by
  unfold b
  suffices h : 17 ≤ largestInducedBipartiteSubgraphSize counterG by
    exact_mod_cast h
  apply le_csSup
  · exact ⟨18, fun n ⟨s, _, hs⟩ => hs ▸ s.card_le_univ⟩
  · refine ⟨Finset.univ.erase (10 : Fin 18), ?_, by decide⟩
    refine ⟨SimpleGraph.Coloring.mk (fun ⟨v, _⟩ => counterColor v) ?_⟩
    intro ⟨u, hu⟩ ⟨v, hv⟩ hadj
    have hu' : u ≠ (10 : Fin 18) := (Finset.mem_erase.mp (Finset.mem_coe.mp hu)).1
    have hv' : v ≠ (10 : Fin 18) := (Finset.mem_erase.mp (Finset.mem_coe.mp hv)).1
    have hadj' : counterG.Adj u v := hadj
    exact counterColor_valid u v hu' hv' hadj'

/-- Construct a triangle cycle. -/
private lemma isCycle_triangle {α : Type*} {G : SimpleGraph α} {u v w : α}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwu : G.Adj w u)
    (hne1 : u ≠ v) (hne2 : v ≠ w) (hne3 : w ≠ u) :
    ∃ p : G.Walk u u, p.IsCycle := by
  let p : G.Walk u u := Walk.cons huv (Walk.cons hvw (Walk.cons hwu Walk.nil))
  refine ⟨p, ?_⟩
  rw [Walk.cons_isCycle_iff]
  constructor
  · rw [Walk.cons_isPath_iff]
    constructor
    · rw [Walk.cons_isPath_iff]
      constructor
      · exact Walk.IsPath.nil
      · simp [hne3]
    · simp [hne1.symm, hne2]
  · simp [SimpleGraph.Walk.edges]
    tauto

/-- Construct a quadrilateral cycle. -/
private lemma isCycle_quad {α : Type*} {G : SimpleGraph α} {a b c d : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hne_ab : a ≠ b) (hne_bc : b ≠ c) (hne_cd : c ≠ d) (hne_da : d ≠ a)
    (hne_ac : a ≠ c) (hne_bd : b ≠ d) :
    ∃ p : G.Walk a a, p.IsCycle := by
  let p : G.Walk a a :=
    Walk.cons hab (Walk.cons hbc (Walk.cons hcd (Walk.cons hda Walk.nil)))
  refine ⟨p, ?_⟩
  rw [Walk.cons_isCycle_iff]
  constructor
  · rw [Walk.cons_isPath_iff]
    constructor
    · rw [Walk.cons_isPath_iff]
      constructor
      · rw [Walk.cons_isPath_iff]
        constructor
        · exact Walk.IsPath.nil
        · simp [hne_da]
      · simp [hne_cd, hne_ac.symm]
    · simp [hne_bc, hne_bd, hne_ab.symm]
  · simp [SimpleGraph.Walk.edges]
    tauto

/-- Construct a hexagon cycle. -/
private lemma isCycle_hexagon {α : Type*} {G : SimpleGraph α} {a b c d e f : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hef : G.Adj e f) (hfa : G.Adj f a)
    (hne_ab : a ≠ b) (hne_ac : a ≠ c) (hne_ad : a ≠ d)
    (hne_ae : a ≠ e) (hne_af : a ≠ f)
    (hne_bc : b ≠ c) (hne_bd : b ≠ d) (hne_be : b ≠ e) (hne_bf : b ≠ f)
    (hne_cd : c ≠ d) (hne_ce : c ≠ e) (hne_cf : c ≠ f)
    (hne_de : d ≠ e) (hne_df : d ≠ f) (hne_ef : e ≠ f) :
    ∃ p : G.Walk a a, p.IsCycle := by
  let p : G.Walk a a := Walk.cons hab <|
    Walk.cons hbc <| Walk.cons hcd <| Walk.cons hde <| Walk.cons hef <|
      Walk.cons hfa Walk.nil
  refine ⟨p, ?_⟩
  rw [Walk.cons_isCycle_iff]
  constructor
  · rw [Walk.cons_isPath_iff]
    constructor
    · rw [Walk.cons_isPath_iff]
      constructor
      · rw [Walk.cons_isPath_iff]
        constructor
        · rw [Walk.cons_isPath_iff]
          constructor
          · rw [Walk.cons_isPath_iff]
            constructor
            · exact Walk.IsPath.nil
            · simp [hne_af.symm]
          · simp [hne_ef, hne_ae.symm]
        · simp [hne_de, hne_df, hne_ad.symm]
      · simp [hne_cd, hne_ce, hne_cf, hne_ac.symm]
    · simp [hne_bc, hne_bd, hne_be, hne_bf, hne_ab.symm]
  · simp [SimpleGraph.Walk.edges]
    tauto

private def Contains3 (s : Finset (Fin 18)) (a b c : Fin 18) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s

private def Contains4 (s : Finset (Fin 18)) (a b c d : Fin 18) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s

private def Contains6 (s : Finset (Fin 18)) (a b c d e f : Fin 18) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧ e ∈ s ∧ f ∈ s

/-- A finite covering certificate: every set of at least 14 vertices contains one
of these 25 fixed cycles. -/
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
private lemma large_subset_cycle_certificate :
    ∀ s : Finset (Fin 18), 14 ≤ s.card →
      Contains3 s 4 7 10 ∨
      Contains4 s 1 5 3 8 ∨
      Contains3 s 0 9 10 ∨
      Contains4 s 2 6 4 9 ∨
      Contains3 s 2 6 10 ∨
      Contains4 s 1 6 3 7 ∨
      Contains4 s 0 5 2 9 ∨
      Contains4 s 1 5 4 6 ∨
      Contains4 s 3 7 4 9 ∨
      Contains4 s 0 5 3 8 ∨
      Contains3 s 1 8 10 ∨
      Contains3 s 3 5 10 ∨
      Contains4 s 0 8 3 9 ∨
      Contains4 s 0 5 1 8 ∨
      Contains4 s 3 6 4 7 ∨
      Contains4 s 1 6 4 7 ∨
      Contains4 s 1 5 4 7 ∨
      Contains4 s 1 6 3 8 ∨
      Contains4 s 1 5 2 6 ∨
      Contains6 s 0 8 1 6 2 9 ∨
      Contains4 s 2 6 3 9 ∨
      Contains4 s 2 5 4 6 ∨
      Contains4 s 1 7 3 8 ∨
      Contains6 s 0 8 1 7 4 9 ∨
      Contains4 s 0 5 4 9 := by
  decide +kernel

private lemma false_of_triangle {s : Finset (Fin 18)} {a b c : Fin 18}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : counterG.Adj a b) (hbc : counterG.Adj b c) (hca : counterG.Adj c a)
    (hne_ab : a ≠ b) (hne_bc : b ≠ c) (hne_ca : c ≠ a)
    (hacyclic : (counterG.induce s).IsAcyclic) : False := by
  let va : s := ⟨a, ha⟩
  let vb : s := ⟨b, hb⟩
  let vc : s := ⟨c, hc⟩
  have hab' : (counterG.induce s).Adj va vb := hab
  have hbc' : (counterG.induce s).Adj vb vc := hbc
  have hca' : (counterG.induce s).Adj vc va := hca
  have hne_ab' : va ≠ vb := fun h => hne_ab (Subtype.ext_iff.mp h)
  have hne_bc' : vb ≠ vc := fun h => hne_bc (Subtype.ext_iff.mp h)
  have hne_ca' : vc ≠ va := fun h => hne_ca (Subtype.ext_iff.mp h)
  obtain ⟨p, hp⟩ := isCycle_triangle hab' hbc' hca' hne_ab' hne_bc' hne_ca'
  exact hacyclic p hp

private lemma false_of_quad {s : Finset (Fin 18)} {a b c d : Fin 18}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : counterG.Adj a b) (hbc : counterG.Adj b c)
    (hcd : counterG.Adj c d) (hda : counterG.Adj d a)
    (hne_ab : a ≠ b) (hne_bc : b ≠ c) (hne_cd : c ≠ d) (hne_da : d ≠ a)
    (hne_ac : a ≠ c) (hne_bd : b ≠ d)
    (hacyclic : (counterG.induce s).IsAcyclic) : False := by
  let va : s := ⟨a, ha⟩
  let vb : s := ⟨b, hb⟩
  let vc : s := ⟨c, hc⟩
  let vd : s := ⟨d, hd⟩
  have hab' : (counterG.induce s).Adj va vb := hab
  have hbc' : (counterG.induce s).Adj vb vc := hbc
  have hcd' : (counterG.induce s).Adj vc vd := hcd
  have hda' : (counterG.induce s).Adj vd va := hda
  have hne_ab' : va ≠ vb := fun h => hne_ab (Subtype.ext_iff.mp h)
  have hne_bc' : vb ≠ vc := fun h => hne_bc (Subtype.ext_iff.mp h)
  have hne_cd' : vc ≠ vd := fun h => hne_cd (Subtype.ext_iff.mp h)
  have hne_da' : vd ≠ va := fun h => hne_da (Subtype.ext_iff.mp h)
  have hne_ac' : va ≠ vc := fun h => hne_ac (Subtype.ext_iff.mp h)
  have hne_bd' : vb ≠ vd := fun h => hne_bd (Subtype.ext_iff.mp h)
  obtain ⟨p, hp⟩ := isCycle_quad hab' hbc' hcd' hda'
    hne_ab' hne_bc' hne_cd' hne_da' hne_ac' hne_bd'
  exact hacyclic p hp

private lemma false_of_hexagon {s : Finset (Fin 18)} {a b c d e f : Fin 18}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hd : d ∈ s) (he : e ∈ s) (hf : f ∈ s)
    (hab : counterG.Adj a b) (hbc : counterG.Adj b c) (hcd : counterG.Adj c d)
    (hde : counterG.Adj d e) (hef : counterG.Adj e f) (hfa : counterG.Adj f a)
    (hne_ab : a ≠ b) (hne_ac : a ≠ c) (hne_ad : a ≠ d)
    (hne_ae : a ≠ e) (hne_af : a ≠ f)
    (hne_bc : b ≠ c) (hne_bd : b ≠ d) (hne_be : b ≠ e) (hne_bf : b ≠ f)
    (hne_cd : c ≠ d) (hne_ce : c ≠ e) (hne_cf : c ≠ f)
    (hne_de : d ≠ e) (hne_df : d ≠ f) (hne_ef : e ≠ f)
    (hacyclic : (counterG.induce s).IsAcyclic) : False := by
  let va : s := ⟨a, ha⟩
  let vb : s := ⟨b, hb⟩
  let vc : s := ⟨c, hc⟩
  let vd : s := ⟨d, hd⟩
  let ve : s := ⟨e, he⟩
  let vf : s := ⟨f, hf⟩
  have hab' : (counterG.induce s).Adj va vb := hab
  have hbc' : (counterG.induce s).Adj vb vc := hbc
  have hcd' : (counterG.induce s).Adj vc vd := hcd
  have hde' : (counterG.induce s).Adj vd ve := hde
  have hef' : (counterG.induce s).Adj ve vf := hef
  have hfa' : (counterG.induce s).Adj vf va := hfa
  have hne_ab' : va ≠ vb := fun h => hne_ab (Subtype.ext_iff.mp h)
  have hne_ac' : va ≠ vc := fun h => hne_ac (Subtype.ext_iff.mp h)
  have hne_ad' : va ≠ vd := fun h => hne_ad (Subtype.ext_iff.mp h)
  have hne_ae' : va ≠ ve := fun h => hne_ae (Subtype.ext_iff.mp h)
  have hne_af' : va ≠ vf := fun h => hne_af (Subtype.ext_iff.mp h)
  have hne_bc' : vb ≠ vc := fun h => hne_bc (Subtype.ext_iff.mp h)
  have hne_bd' : vb ≠ vd := fun h => hne_bd (Subtype.ext_iff.mp h)
  have hne_be' : vb ≠ ve := fun h => hne_be (Subtype.ext_iff.mp h)
  have hne_bf' : vb ≠ vf := fun h => hne_bf (Subtype.ext_iff.mp h)
  have hne_cd' : vc ≠ vd := fun h => hne_cd (Subtype.ext_iff.mp h)
  have hne_ce' : vc ≠ ve := fun h => hne_ce (Subtype.ext_iff.mp h)
  have hne_cf' : vc ≠ vf := fun h => hne_cf (Subtype.ext_iff.mp h)
  have hne_de' : vd ≠ ve := fun h => hne_de (Subtype.ext_iff.mp h)
  have hne_df' : vd ≠ vf := fun h => hne_df (Subtype.ext_iff.mp h)
  have hne_ef' : ve ≠ vf := fun h => hne_ef (Subtype.ext_iff.mp h)
  obtain ⟨p, hp⟩ := isCycle_hexagon hab' hbc' hcd' hde' hef' hfa'
    hne_ab' hne_ac' hne_ad' hne_ae' hne_af'
    hne_bc' hne_bd' hne_be' hne_bf'
    hne_cd' hne_ce' hne_cf' hne_de' hne_df' hne_ef'
  exact hacyclic p hp

/-- Every induced forest has at most 13 vertices. -/
private lemma counterG_forest_le : counterG.largestInducedForestSize ≤ 13 := by
  apply csSup_le
  · refine ⟨0, ∅, ?_, rfl⟩
    intro ⟨v, hv⟩
    simp at hv
  · rintro n ⟨s, hacyclic, rfl⟩
    by_contra hle
    have hcard : 14 ≤ s.card := by omega
    rcases large_subset_cycle_certificate s hcard with
      h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 |
      h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 |
      h21 | h22 | h23 | h24 | h25
    · rcases h1 with ⟨h4, h7, h10⟩
      exact false_of_triangle h4 h7 h10 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hacyclic
    · rcases h2 with ⟨h1, h5, h3, h8⟩
      exact false_of_quad h1 h5 h3 h8 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h3 with ⟨h0, h9, h10⟩
      exact false_of_triangle h0 h9 h10 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hacyclic
    · rcases h4 with ⟨h2, h6, h4, h9⟩
      exact false_of_quad h2 h6 h4 h9 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h5 with ⟨h2, h6, h10⟩
      exact false_of_triangle h2 h6 h10 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hacyclic
    · rcases h6 with ⟨h1, h6, h3, h7⟩
      exact false_of_quad h1 h6 h3 h7 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h7 with ⟨h0, h5, h2, h9⟩
      exact false_of_quad h0 h5 h2 h9 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h8 with ⟨h1, h5, h4, h6⟩
      exact false_of_quad h1 h5 h4 h6 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h9 with ⟨h3, h7, h4, h9⟩
      exact false_of_quad h3 h7 h4 h9 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h10 with ⟨h0, h5, h3, h8⟩
      exact false_of_quad h0 h5 h3 h8 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h11 with ⟨h1, h8, h10⟩
      exact false_of_triangle h1 h8 h10 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hacyclic
    · rcases h12 with ⟨h3, h5, h10⟩
      exact false_of_triangle h3 h5 h10 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hacyclic
    · rcases h13 with ⟨h0, h8, h3, h9⟩
      exact false_of_quad h0 h8 h3 h9 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h14 with ⟨h0, h5, h1, h8⟩
      exact false_of_quad h0 h5 h1 h8 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h15 with ⟨h3, h6, h4, h7⟩
      exact false_of_quad h3 h6 h4 h7 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h16 with ⟨h1, h6, h4, h7⟩
      exact false_of_quad h1 h6 h4 h7 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h17 with ⟨h1, h5, h4, h7⟩
      exact false_of_quad h1 h5 h4 h7 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h18 with ⟨h1, h6, h3, h8⟩
      exact false_of_quad h1 h6 h3 h8 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h19 with ⟨h1, h5, h2, h6⟩
      exact false_of_quad h1 h5 h2 h6 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h20 with ⟨h0, h8, h1, h6, h2, h9⟩
      exact false_of_hexagon h0 h8 h1 h6 h2 h9
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hacyclic
    · rcases h21 with ⟨h2, h6, h3, h9⟩
      exact false_of_quad h2 h6 h3 h9 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h22 with ⟨h2, h5, h4, h6⟩
      exact false_of_quad h2 h5 h4 h6 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h23 with ⟨h1, h7, h3, h8⟩
      exact false_of_quad h1 h7 h3 h8 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic
    · rcases h24 with ⟨h0, h8, h1, h7, h4, h9⟩
      exact false_of_hexagon h0 h8 h1 h7 h4 h9
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hacyclic
    · rcases h25 with ⟨h0, h5, h4, h9⟩
      exact false_of_quad h0 h5 h4 h9 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hacyclic

set_option linter.style.ams_attribute true
set_option linter.style.category_attribute true

/--
WOWII Conjecture 59 is false.  The counterexample is the 18-vertex graph
specified in the module docstring.
-/
@[category research solved, AMS 5]
theorem conjecture59 : answer(False) ↔
    ∀ (α : Type*) [Fintype α] [DecidableEq α] [Nontrivial α]
      (G : SimpleGraph α) [DecidableRel G.Adj] (_h : G.Connected),
      ⌈Real.sqrt ((residue G : ℝ) * b G)⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  constructor
  · intro h
    exact h.elim
  · intro hP
    have hineq := hP (Fin 18) counterG counterG_connected
    have hf : (counterG.largestInducedForestSize : ℝ) ≤ 13 := by
      exact_mod_cast counterG_forest_le
    have hprod : (170 : ℝ) ≤ (residue counterG : ℝ) * b counterG := by
      calc
        (170 : ℝ) = 10 * 17 := by norm_num
        _ ≤ 10 * b counterG := mul_le_mul_of_nonneg_left counterG_b_ge (by norm_num)
        _ = (residue counterG : ℝ) * b counterG := by rw [counterG_residue]; norm_num
    have hsqrt170 : (13 : ℝ) < Real.sqrt 170 := by
      rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 13)]
      norm_num
    have hsqrt : (13 : ℝ) < Real.sqrt ((residue counterG : ℝ) * b counterG) :=
      hsqrt170.trans_le (Real.sqrt_le_sqrt hprod)
    have hceilInt : (13 : ℤ) < ⌈Real.sqrt ((residue counterG : ℝ) * b counterG)⌉ := by
      rw [Int.lt_ceil]
      simpa using hsqrt
    have hceil : (13 : ℝ) < (⌈Real.sqrt ((residue counterG : ℝ) * b counterG)⌉ : ℝ) := by
      exact_mod_cast hceilInt
    linarith

end WrittenOnTheWallII.GraphConjecture59
