/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SpanningTree
import Lean.Elab.Tactic.Omega

open Classical Finset
namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The subgraph consisting of all edges of `G` incident to `v`. -/
def incidentStar (G : SimpleGraph α) (v : α) : SimpleGraph α where
  Adj x y := G.Adj x y ∧ (x = v ∨ y = v)
  symm := by
    intro x y h
    refine ⟨G.symm h.1, ?_⟩
    rcases h.2 with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  loopless := by
    intro x h
    exact G.loopless x h.1

@[simp] theorem incidentStar_adj (G : SimpleGraph α) (v x y : α) :
    (incidentStar G v).Adj x y ↔ G.Adj x y ∧ (x = v ∨ y = v) := Iff.rfl

theorem incidentStar_le (G : SimpleGraph α) (v : α) : incidentStar G v ≤ G :=
  fun _ _ h => h.1

@[simp] theorem incidentStar_neighborSet_center (G : SimpleGraph α) (v : α) :
    (incidentStar G v).neighborSet v = G.neighborSet v := by
  ext x
  simp [incidentStar]

@[simp] theorem incidentStar_degree_center (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    (incidentStar G v).degree v = G.degree v := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact Fintype.card_congr (Equiv.setCongr (incidentStar_neighborSet_center G v))

lemma incidentStar_isAcyclic (G : SimpleGraph α) (v : α) : (incidentStar G v).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro x y hxy
  rw [isBridge_iff_adj_and_forall_walk_mem_edges]
  refine ⟨hxy, ?_⟩
  intro p
  have hne : x ≠ y := hxy.ne
  have hnil : ¬p.Nil := p.not_nil_of_ne hne
  rcases hxy.2 with hx | hy
  · subst x
    have hlast := p.adj_penultimate hnil
    have hyne : y ≠ v := by
      intro h
      subst y
      exact hne rfl
    have hpen : p.penultimate = v := by
      rcases hlast.2 with h | h
      · exact h
      · exact (hyne h).elim
    simpa [hpen] using p.mk_penultimate_end_mem_edges hnil
  · subst y
    have hfirst := p.adj_snd hnil
    have hxne : x ≠ v := by
      intro h
      subst x
      exact hne rfl
    have hsnd : p.snd = v := by
      rcases hfirst.2 with h | h
      · exact (hxne h).elim
      · exact h
    simpa [hsnd] using p.mk_start_snd_mem_edges hnil

/-- Every connected graph has a spanning tree containing the full incident star at `v`. -/
theorem Connected.exists_isTree_le_containing_incidentStar (G : SimpleGraph α) (v : α)
    (hG : G.Connected) :
    ∃ T : SimpleGraph α, incidentStar G v ≤ T ∧ T ≤ G ∧ T.IsTree := by
  obtain ⟨T, hstarT, hmax⟩ :=
    exists_maximal_isAcyclic_of_le_isAcyclic (incidentStar_le G v) (incidentStar_isAcyclic G v)
  exact ⟨T, hstarT, hmax.1.1, (hG.maximal_le_isAcyclic_iff_isTree hmax.1.1).mp hmax⟩

lemma IsTree.degree_le_leaf_card [Nontrivial α] (T : SimpleGraph α) [DecidableRel T.Adj]
    (hT : T.IsTree) (v : α) :
    T.degree v ≤ (Finset.univ.filter fun x => T.degree x = 1).card := by
  let deg : α → ℕ := fun x => T.degree x
  let L : Finset α := Finset.univ.filter fun x => deg x = 1
  change deg v ≤ L.card
  by_cases hv : deg v = 1
  · have hvL : v ∈ L := by simp [L, hv]
    have hpos : 0 < L.card := Finset.card_pos.mpr ⟨v, hvL⟩
    omega
  · let R : Finset α := Finset.univ.erase v
    let A : Finset α := R.filter fun x => deg x = 1
    let B : Finset α := R.filter fun x => deg x ≠ 1
    have hA : A = L := by
      apply Finset.ext
      intro x
      constructor
      · intro hx
        have hxA := Finset.mem_filter.mp
          (show x ∈ R.filter (fun y => deg y = 1) by simpa [A] using hx)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxA.2⟩
      · intro hx
        have hxL := Finset.mem_filter.mp
          (show x ∈ Finset.univ.filter (fun y => deg y = 1) by simpa [L] using hx)
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_erase.mpr
          constructor
          · intro hxv
            subst x
            exact hv hxL.2
          · exact Finset.mem_univ _
        · exact hxL.2
    have hBdeg : ∀ x ∈ B, 2 ≤ deg x := by
      intro x hx
      have hxne : deg x ≠ 1 := (Finset.mem_filter.mp
        (show x ∈ R.filter (fun y => deg y ≠ 1) by simpa [B] using hx)).2
      have hxpos : 0 < deg x := by
        dsimp [deg]
        exact hT.isConnected.preconnected.degree_pos_of_nontrivial x
      omega
    have hBsum : 2 * B.card ≤ ∑ x ∈ B, deg x := by
      calc
        2 * B.card = ∑ x ∈ B, 2 := by simp [mul_comm]
        _ ≤ ∑ x ∈ B, deg x := Finset.sum_le_sum fun x hx => hBdeg x hx
    have hAsum : ∑ x ∈ A, deg x = A.card := by
      calc
        (∑ x ∈ A, deg x) = ∑ x ∈ A, 1 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact (Finset.mem_filter.mp
            (show x ∈ R.filter (fun y => deg y = 1) by simpa [A] using hx)).2
        _ = A.card := by simp
    have hpartition :
        (∑ x ∈ R, deg x) = (∑ x ∈ A, deg x) + ∑ x ∈ B, deg x := by
      have h := Finset.sum_ite (s := R) (p := fun x => deg x = 1)
        (fun x => deg x) (fun x => deg x)
      simp only [ite_self] at h
      simpa [A, B] using h
    have hRcard : R.card + 1 = Fintype.card α := by
      rw [show R = Finset.univ.erase v by rfl,
        Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
      have hc : 0 < Fintype.card α := Fintype.card_pos
      omega
    have hABcard : A.card + B.card = R.card := by
      simpa [A, B] using
        (Finset.filter_card_add_filter_neg_card_eq_card (s := R) (p := fun x => deg x = 1))
    have hsumdeg := T.sum_degrees_eq_twice_card_edges
    change (∑ x, deg x) = 2 * T.edgeFinset.card at hsumdeg
    have hedges := hT.card_edgeFinset
    have herase := Finset.sum_erase_add Finset.univ deg (Finset.mem_univ v)
    rw [hpartition, hAsum] at herase
    rw [hA] at hABcard herase
    omega

noncomputable def leafCount {G : SimpleGraph α} [DecidableRel G.Adj]
    (T : G.Subgraph) : ℕ :=
  (T.verts.toFinset.filter fun v => T.degree v = 1).card

theorem leafCount_le_Ls (G : SimpleGraph α) [DecidableRel G.Adj]
    (T : Subgraph G) (hT : T.IsSpanning ∧ IsTree T.coe) :
    (leafCount T : ℝ) ≤ Ls G := by
  unfold leafCount Ls
  apply le_csSup
  · exact (Set.toFinite _).bddAbove
  · exact ⟨T, hT, rfl⟩

/-- Every vertex degree is bounded by the maximum number of leaves of a spanning
 tree in a connected finite graph. -/
theorem degree_cast_le_Ls_of_connected [Nontrivial α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hG : G.Connected) (v : α) :
    (G.degree v : ℝ) ≤ Ls G := by
  obtain ⟨T, hstarT, hTG, hT⟩ := hG.exists_isTree_le_containing_incidentStar G v
  have hdegStar : (incidentStar G v).degree v ≤ T.degree v := degree_le_of_le hstarT
  have hdegGT : G.degree v ≤ T.degree v := by simpa using hdegStar
  have hdegLeaves : T.degree v ≤ (Finset.univ.filter fun x => T.degree x = 1).card :=
    hT.degree_le_leaf_card T v
  let ST : G.Subgraph := G.toSubgraph T hTG
  have hSTspanning : ST.IsSpanning := SimpleGraph.toSubgraph.isSpanning T hTG
  have hSTtree : ST.coe.IsTree := by
    have hspanTree : ST.spanningCoe.IsTree := by
      simpa [ST, SimpleGraph.Subgraph.spanningCoe] using hT
    exact (ST.spanningCoeEquivCoeOfSpanning hSTspanning).isTree_iff.mp hspanTree
  have hleaf := leafCount_le_Ls G ST ⟨hSTspanning, hSTtree⟩
  have hleafFinsetEq :
      (ST.verts.toFinset.filter fun x => ST.degree x = 1) =
        (Finset.univ.filter fun x => T.degree x = 1) := by
    ext x
    simp [ST, SimpleGraph.degree_toSubgraph]
  have hleafEq := congrArg Finset.card hleafFinsetEq
  change ((ST.verts.toFinset.filter fun x => ST.degree x = 1).card : ℝ) ≤ Ls G at hleaf
  rw [hleafEq] at hleaf
  exact (Nat.cast_le.mpr (hdegGT.trans hdegLeaves)).trans hleaf

#print axioms SimpleGraph.degree_cast_le_Ls_of_connected

end SimpleGraph
