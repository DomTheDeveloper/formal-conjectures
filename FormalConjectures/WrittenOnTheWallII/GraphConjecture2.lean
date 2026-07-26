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

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture2

open Classical SimpleGraph Finset BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

private def starEdges (v : α) (S : Finset α) : SimpleGraph α :=
  S.sup fun s => edge v s

private lemma starEdges_adj_iff (v a b : α) (S : Finset α) :
    (starEdges v S).Adj a b ↔
      ((a = v ∧ b ∈ S) ∨ (a ∈ S ∧ b = v)) ∧ a ≠ b := by
  induction S using Finset.induction_on with
  | empty => simp [starEdges]
  | @insert s S hs ih =>
      rw [starEdges, Finset.sup_insert, sup_adj, edge_adj]
      simp only [Finset.mem_insert]
      simp only [starEdges] at ih
      rw [ih]
      aesop

private lemma starEdges_isAcyclic (v : α) (S : Finset α) (hv : v ∉ S) :
    (starEdges v S).IsAcyclic := by
  induction S using Finset.induction_on with
  | empty => simpa [starEdges] using (isAcyclic_bot : (⊥ : SimpleGraph α).IsAcyclic)
  | @insert s S hs ih =>
      have hsv : s ≠ v := by
        intro hsv
        subst s
        exact hv (Finset.mem_insert_self _ _)
      have hvS : v ∉ S := by
        intro hvS
        exact hv (Finset.mem_insert_of_mem hvS)
      rw [starEdges, Finset.sup_insert, sup_comm]
      apply (isAcyclic_add_edge_iff_of_not_reachable v s ?_).2
      · simpa [starEdges] using ih hvS
      · intro hreach
        rcases hreach with ⟨p⟩
        have hpnil : ¬p.Nil := p.not_nil_of_ne hsv.symm
        have hadj : (starEdges v S).Adj p.penultimate s := p.adj_penultimate hpnil
        rw [starEdges_adj_iff] at hadj
        rcases hadj.1 with h | h
        · exact hs h.2
        · exact hsv h.2

private lemma starEdges_le (G : SimpleGraph α) (v : α) (S : Finset α)
    (hS : ∀ s ∈ S, G.Adj v s) : starEdges v S ≤ G := by
  unfold starEdges
  apply Finset.sup_le
  intro s hs
  rw [edge_le_iff]
  exact Or.inr (hS s hs)

private lemma IsAcyclic.sup_starEdges_of_isolated
    (F : SimpleGraph α) (y : α) (B : Finset α)
    (hF : F.IsAcyclic)
    (hyB : ∀ b ∈ B, b ≠ y)
    (hiso : ∀ b ∈ B, ∀ z, ¬F.Adj z b) :
    (F ⊔ starEdges y B).IsAcyclic := by
  induction B using Finset.induction_on with
  | empty => simpa [starEdges] using hF
  | @insert b B hb ih =>
      have hby : b ≠ y := hyB b (Finset.mem_insert_self _ _)
      have hyB' : ∀ c ∈ B, c ≠ y := by
        intro c hc
        exact hyB c (Finset.mem_insert_of_mem hc)
      have hiso' : ∀ c ∈ B, ∀ z, ¬F.Adj z c := by
        intro c hc z
        exact hiso c (Finset.mem_insert_of_mem hc) z
      have hprev : (F ⊔ starEdges y B).IsAcyclic := ih hyB' hiso'
      rw [starEdges, Finset.sup_insert]
      change (F ⊔ (edge y b ⊔ starEdges y B)).IsAcyclic
      rw [sup_comm (edge y b) (starEdges y B), ← sup_assoc]
      apply (isAcyclic_add_edge_iff_of_not_reachable y b ?_).2 hprev
      intro hreach
      rcases hreach with ⟨p⟩
      have hpnil : ¬p.Nil := p.not_nil_of_ne hby.symm
      have hadj : (F ⊔ starEdges y B).Adj p.penultimate b := p.adj_penultimate hpnil
      rw [sup_adj] at hadj
      rcases hadj with hadjF | hadjS
      · exact hiso b (Finset.mem_insert_self _ _) p.penultimate hadjF
      · rw [starEdges_adj_iff] at hadjS
        rcases hadjS.1 with h | h
        · exact hb h.2
        · exact hby h.2

private lemma doubleStar_exists
    (G : SimpleGraph α) [DecidableRel G.Adj]
    {x y : α} (hxy : G.Adj x y) :
    ∃ H : SimpleGraph α,
      H ≤ G ∧ H.IsAcyclic ∧ H.Adj x y ∧
      (G.neighborFinset x ∪ G.neighborFinset y).card - 2 ≤
        H.degree x + H.degree y - 2 := by
  classical
  let Nx : Finset α := G.neighborFinset x
  let Ny : Finset α := G.neighborFinset y
  let A : Finset α := Nx.erase y
  let D : Finset α := Ny \ Nx
  let B : Finset α := D.erase x
  let C : Finset α := insert y A
  let F : SimpleGraph α := starEdges x C
  let H : SimpleGraph α := F ⊔ starEdges y B
  letI : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  have hxyne : x ≠ y := hxy.ne
  have hyNx : y ∈ Nx := by simpa [Nx] using hxy
  have hxNy : x ∈ Ny := by simpa [Ny] using hxy.symm
  have hxNx : x ∉ Nx := by simpa [Nx] using G.notMem_neighborFinset_self x
  have hyNy : y ∉ Ny := by simpa [Ny] using G.notMem_neighborFinset_self y
  have hxD : x ∈ D := by simp [D, hxNy, hxNx]
  have hxB : x ∉ B := by simp [B]
  have hyB : y ∉ B := by
    intro hy
    have hyD : y ∈ D := Finset.mem_of_mem_erase hy
    have hyD' : y ∈ Ny ∧ y ∉ Nx := by
      exact Finset.mem_sdiff.mp (by simpa [D] using hyD)
    exact hyNy hyD'.1
  have hxC : x ∉ C := by
    simp [C, A, hxyne, hxNx]
  have hFacyc : F.IsAcyclic := by
    simpa [F] using starEdges_isAcyclic x C hxC
  have hBnotC : ∀ b ∈ B, b ∉ C := by
    intro b hb hbC
    have hbD : b ∈ D := Finset.mem_of_mem_erase hb
    have hbD' : b ∈ Ny ∧ b ∉ Nx := by
      exact Finset.mem_sdiff.mp (by simpa [D] using hbD)
    have hbnotNx : b ∉ Nx := hbD'.2
    rcases Finset.mem_insert.mp hbC with rfl | hbA
    · exact hyB hb
    · exact hbnotNx (Finset.mem_of_mem_erase hbA)
  have hBneX : ∀ b ∈ B, b ≠ x := by
    intro b hb hbx
    subst b
    exact hxB hb
  have hBneY : ∀ b ∈ B, b ≠ y := by
    intro b hb hby
    subst b
    exact hyB hb
  have hIsoF : ∀ b ∈ B, ∀ z, ¬F.Adj z b := by
    intro b hb z hzb
    change (starEdges x C).Adj z b at hzb
    rw [starEdges_adj_iff] at hzb
    rcases hzb.1 with h | h
    · exact (hBnotC b hb) h.2
    · exact (hBneX b hb) h.2
  have hHacyc : H.IsAcyclic := by
    simpa [H] using
      IsAcyclic.sup_starEdges_of_isolated F y B hFacyc hBneY hIsoF
  have hFle : F ≤ G := by
    apply starEdges_le G x C
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hsA
    · exact hxy
    · have hsNx : s ∈ Nx := Finset.mem_of_mem_erase hsA
      simpa [Nx] using hsNx
  have hBle : starEdges y B ≤ G := by
    apply starEdges_le G y B
    intro b hb
    have hbD : b ∈ D := Finset.mem_of_mem_erase hb
    have hbD' : b ∈ Ny ∧ b ∉ Nx := by
      exact Finset.mem_sdiff.mp (by simpa [D] using hbD)
    have hbNy : b ∈ Ny := hbD'.1
    simpa [Ny] using hbNy
  have hHle : H ≤ G := by
    simpa [H] using sup_le hFle hBle
  have hCx : C.card = A.card + 1 := by
    rw [Finset.card_insert_of_notMem]
    simp [A, hyNx]
  have hBD : B.card + 1 = D.card := Finset.card_erase_add_one hxD
  have hANx : A.card + 1 = Nx.card := Finset.card_erase_add_one hyNx
  have hDisj : Disjoint Nx D := by
    rw [Finset.disjoint_left]
    intro z hzNx hzD
    have hzD' : z ∈ Ny ∧ z ∉ Nx := by
      exact Finset.mem_sdiff.mp (by simpa [D] using hzD)
    exact hzD'.2 hzNx
  have hUnion : Nx ∪ D = Nx ∪ Ny := by
    ext z
    simp [D]
  have hCardUnion : (Nx ∪ Ny).card = Nx.card + D.card := by
    rw [← hUnion, Finset.card_union_of_disjoint hDisj]
  have hdegX : H.degree x = C.card := by
    rw [← card_neighborFinset_eq_degree]
    congr 1
    ext z
    rw [mem_neighborFinset]
    change ((starEdges x C ⊔ starEdges y B).Adj x z ↔ z ∈ C)
    rw [sup_adj, starEdges_adj_iff, starEdges_adj_iff]
    simp only [true_and]
    constructor
    · rintro (⟨h | h, hxz⟩ | ⟨h | h, hxz⟩)
      · exact h
      · exact (hxC h.1).elim
      · exact (hxyne h.1).elim
      · exact (hxB h.1).elim
    · intro hz
      exact Or.inl ⟨Or.inl hz, fun hxz => hxC (hxz ▸ hz)⟩
  have hdegY : H.degree y = B.card + 1 := by
    rw [← card_neighborFinset_eq_degree]
    have hfin : H.neighborFinset y = insert x B := by
      ext z
      rw [mem_neighborFinset]
      change ((starEdges x C ⊔ starEdges y B).Adj y z ↔ z ∈ insert x B)
      rw [sup_adj, starEdges_adj_iff, starEdges_adj_iff]
      simp only [Finset.mem_insert, true_and]
      constructor
      · rintro (⟨h | h, hyz⟩ | ⟨h | h, hyz⟩)
        · exact (hxyne h.1.symm).elim
        · exact Or.inl h.2
        · exact Or.inr h
        · exact (hyB h.1).elim
      · intro hz
        rcases hz with rfl | hzB
        · exact Or.inl ⟨Or.inr ⟨Finset.mem_insert_self _ _, rfl⟩, hxyne.symm⟩
        · exact Or.inr ⟨Or.inl hzB, fun hyz => hyB (hyz ▸ hzB)⟩
    rw [hfin, Finset.card_insert_of_notMem hxB]
  have hbound : (Nx ∪ Ny).card - 2 ≤ H.degree x + H.degree y - 2 := by
    rw [hdegX, hdegY]
    omega
  refine ⟨H, hHle, hHacyc, ?_, ?_⟩
  · unfold H F C
    rw [sup_adj]
    left
    rw [starEdges_adj_iff]
    exact ⟨Or.inl ⟨rfl, Finset.mem_insert_self _ _⟩, hxyne⟩
  · simpa only [Nx, Ny] using hbound

private lemma Connected.exists_isTree_extension
    {G H : SimpleGraph α} (hG : G.Connected)
    (hHG : H ≤ G) (hHacyc : H.IsAcyclic) :
    ∃ T : SimpleGraph α, H ≤ T ∧ T ≤ G ∧ T.IsTree := by
  classical
  obtain ⟨T, hHT, hTmax⟩ :=
    Finite.exists_le_maximal (α := SimpleGraph α)
      (p := fun F => F ≤ G ∧ F.IsAcyclic) ⟨hHG, hHacyc⟩
  have hTG : T ≤ G := hTmax.prop.1
  have hTtree : T.IsTree :=
    (hG.maximal_le_isAcyclic_iff_isTree hTG).1 hTmax
  exact ⟨T, hHT, hTG, hTtree⟩

private lemma degree_le_leafCount_of_isTree
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (x : α) :
    T.degree x ≤ (Finset.univ.filter fun v => T.degree v = 1).card := by
  classical
  let leaves : Finset α := Finset.univ.filter fun v => T.degree v = 1
  by_cases hx : T.degree x = 1
  · have hxmem : x ∈ leaves := by simp [leaves, hx]
    have hcard : 1 ≤ leaves.card := Finset.one_le_card.mpr ⟨x, hxmem⟩
    simpa [leaves, hx] using hcard
  · let s : Finset α := Finset.univ.erase x
    let nonleaves : Finset α := s.filter fun v => T.degree v ≠ 1
    let leavesAway : Finset α := s.filter fun v => T.degree v = 1
    have hpos (v : α) : 0 < T.degree v :=
      hT.isConnected.preconnected.degree_pos_of_nontrivial v
    have hlower :
        leavesAway.card + 2 * nonleaves.card ≤ ∑ v ∈ s, T.degree v := by
      have hpoint :
          (∑ v ∈ s, if T.degree v = 1 then (1 : ℕ) else 2) ≤
            ∑ v ∈ s, T.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        split_ifs with hvone
        · omega
        · have hvpos := hpos v
          omega
      have hsumite :
          (∑ v ∈ s, if T.degree v = 1 then (1 : ℕ) else 2) =
            leavesAway.card + 2 * nonleaves.card := by
        rw [Finset.sum_ite]
        simp [leavesAway, nonleaves, Nat.mul_comm]
      rwa [hsumite] at hpoint
    have hpartition : leavesAway.card + nonleaves.card = s.card := by
      simpa [leavesAway, nonleaves] using
        (Finset.card_filter_add_card_filter_not
          (s := s) (fun v => T.degree v = 1))
    have hsumErase :
        (∑ v ∈ s, T.degree v) + T.degree x = ∑ v : α, T.degree v := by
      simpa [s] using
        (Finset.sum_erase_add (Finset.univ : Finset α) (fun v => T.degree v)
          (Finset.mem_univ x))
    have hsumDeg : (∑ v : α, T.degree v) = 2 * T.edgeFinset.card :=
      T.sum_degrees_eq_twice_card_edges
    have hedge : T.edgeFinset.card + 1 = Fintype.card α := hT.card_edgeFinset
    have hcardS : s.card + 1 = Fintype.card α := by
      simpa [s] using Finset.card_erase_add_one (Finset.mem_univ x)
    have hleafEq : leaves.card = leavesAway.card := by
      unfold leaves leavesAway s
      rw [Finset.filter_erase]
      simp [hx]
    rw [hleafEq]
    omega

private lemma adjacent_degree_sum_sub_two_le_leafCount_of_isTree
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    {x y : α} (hxy : T.Adj x y) :
    T.degree x + T.degree y - 2 ≤
      (Finset.univ.filter fun v => T.degree v = 1).card := by
  classical
  let leaves : Finset α := Finset.univ.filter fun v => T.degree v = 1
  by_cases hx : T.degree x = 1
  · have hybound := degree_le_leafCount_of_isTree T hT y
    omega
  by_cases hy : T.degree y = 1
  · have hxbound := degree_le_leafCount_of_isTree T hT x
    omega
  have hxyne : x ≠ y := hxy.ne
  let sx : Finset α := Finset.univ.erase x
  let s : Finset α := sx.erase y
  let nonleaves : Finset α := s.filter fun v => T.degree v ≠ 1
  let leavesAway : Finset α := s.filter fun v => T.degree v = 1
  have hpos (v : α) : 0 < T.degree v :=
    hT.isConnected.preconnected.degree_pos_of_nontrivial v
  have hlower :
      leavesAway.card + 2 * nonleaves.card ≤ ∑ v ∈ s, T.degree v := by
    have hpoint :
        (∑ v ∈ s, if T.degree v = 1 then (1 : ℕ) else 2) ≤
          ∑ v ∈ s, T.degree v := by
      apply Finset.sum_le_sum
      intro v hv
      split_ifs with hvone
      · omega
      · have hvpos := hpos v
        omega
    have hsumite :
        (∑ v ∈ s, if T.degree v = 1 then (1 : ℕ) else 2) =
          leavesAway.card + 2 * nonleaves.card := by
      rw [Finset.sum_ite]
      simp [leavesAway, nonleaves, Nat.mul_comm]
    rwa [hsumite] at hpoint
  have hpartition : leavesAway.card + nonleaves.card = s.card := by
    simpa [leavesAway, nonleaves] using
      (Finset.card_filter_add_card_filter_not
        (s := s) (fun v => T.degree v = 1))
  have hyMem : y ∈ sx := by simp [sx, hxyne.symm]
  have hsumY :
      (∑ v ∈ s, T.degree v) + T.degree y = ∑ v ∈ sx, T.degree v := by
    simpa [s] using Finset.sum_erase_add sx (fun v => T.degree v) hyMem
  have hsumX :
      (∑ v ∈ sx, T.degree v) + T.degree x = ∑ v : α, T.degree v := by
    simpa [sx] using
      (Finset.sum_erase_add (Finset.univ : Finset α) (fun v => T.degree v)
        (Finset.mem_univ x))
  have hsumDeg : (∑ v : α, T.degree v) = 2 * T.edgeFinset.card :=
    T.sum_degrees_eq_twice_card_edges
  have hedge : T.edgeFinset.card + 1 = Fintype.card α := hT.card_edgeFinset
  have hcardY : s.card + 1 = sx.card := by
    simpa [s] using Finset.card_erase_add_one hyMem
  have hcardX : sx.card + 1 = Fintype.card α := by
    simpa [sx] using Finset.card_erase_add_one (Finset.mem_univ x)
  have hleafEq : leaves.card = leavesAway.card := by
    unfold leaves leavesAway s sx
    rw [Finset.filter_erase, Finset.filter_erase]
    simp [hx, hy]
  change T.degree x + T.degree y - 2 ≤ leaves.card
  rw [hleafEq]
  omega

private noncomputable def leafCount {G : SimpleGraph α} [DecidableRel G.Adj]
    (T : G.Subgraph) : ℕ :=
  (T.verts.toFinset.filter fun v => T.degree v = 1).card

private lemma leafCount_le_Ls (G : SimpleGraph α) [DecidableRel G.Adj]
    (T : G.Subgraph) (hTspan : T.IsSpanning) (hTtree : IsTree T.coe) :
    (leafCount T : ℝ) ≤ Ls G := by
  unfold leafCount Ls
  apply le_csSup
  · refine ⟨(Fintype.card α : ℝ), ?_⟩
    rintro z ⟨S, _hS, rfl⟩
    have hcard :
        (S.verts.toFinset.filter fun v => S.degree v = 1).card ≤ Fintype.card α :=
      Finset.card_le_univ _
    have hcast :
        ((S.verts.toFinset.filter fun v => S.degree v = 1).card : ℝ) ≤
          (Fintype.card α : ℝ) := by
      exact_mod_cast hcard
    simpa using hcast
  · exact ⟨T, ⟨hTspan, hTtree⟩, rfl⟩

private lemma neighbor_union_ncard_eq_card
    (G : SimpleGraph α) [DecidableRel G.Adj] (x y : α) :
    Set.ncard (G.neighborSet x ∪ G.neighborSet y) =
      (G.neighborFinset x ∪ G.neighborFinset y).card := by
  let hs : (G.neighborSet x ∪ G.neighborSet y).Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hs]
  apply congrArg Finset.card
  ext z
  rw [hs.mem_toFinset, Finset.mem_union, mem_neighborFinset, mem_neighborFinset,
    Set.mem_union, mem_neighborSet, mem_neighborSet]

private lemma adjacent_neighbor_union_le_Ls_add_two
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    {x y : α} (hxy : G.Adj x y) :
    (Set.ncard (G.neighborSet x ∪ G.neighborSet y) : ℝ) ≤ Ls G + 2 := by
  classical
  obtain ⟨H, hHG, hHacyc, hHxy, hdouble⟩ := doubleStar_exists G hxy
  obtain ⟨T, hHT, hTG, hTtree⟩ :=
    Connected.exists_isTree_extension (G := G) (H := H) hG hHG hHacyc
  letI : DecidableRel T.Adj := fun _ _ => Classical.propDecidable _
  have hTxy : T.Adj x y := hHT hHxy
  have hxdeg : H.degree x ≤ T.degree x := degree_le_of_le hHT
  have hydeg : H.degree y ≤ T.degree y := degree_le_of_le hHT
  have hdoubleT :
      (G.neighborFinset x ∪ G.neighborFinset y).card - 2 ≤
        T.degree x + T.degree y - 2 := by
    omega
  have htreeLeaves :
      T.degree x + T.degree y - 2 ≤
        (Finset.univ.filter fun v => T.degree v = 1).card :=
    adjacent_degree_sum_sub_two_le_leafCount_of_isTree T hTtree hTxy
  have hsub : ({x, y} : Finset α) ⊆
      G.neighborFinset x ∪ G.neighborFinset y := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_union_right _ (by simpa using hxy.symm)
    · exact Finset.mem_union_left _ (by simpa using hxy)
  have htwo : 2 ≤ (G.neighborFinset x ∪ G.neighborFinset y).card := by
    have hc := Finset.card_le_card hsub
    simpa [hxy.ne] using hc
  have hnat :
      (G.neighborFinset x ∪ G.neighborFinset y).card ≤
        (Finset.univ.filter fun v => T.degree v = 1).card + 2 := by
    omega
  let Tsub : G.Subgraph := G.toSubgraph T hTG
  have hspan : Tsub.IsSpanning := SimpleGraph.toSubgraph.isSpanning T hTG
  have hspanCoe : Tsub.spanningCoe = T := by rfl
  have hcoetree : Tsub.coe.IsTree := by
    have hsptree : Tsub.spanningCoe.IsTree := by
      simpa [hspanCoe] using hTtree
    exact (Tsub.spanningCoeEquivCoeOfSpanning hspan).isTree_iff.mp hsptree
  have hleafEq :
      (Finset.univ.filter fun v => T.degree v = 1).card = leafCount Tsub := by
    unfold leafCount
    simp [Tsub, degree_toSubgraph]
  have hnat' :
      (G.neighborFinset x ∪ G.neighborFinset y).card ≤ leafCount Tsub + 2 := by
    rwa [hleafEq] at hnat
  calc
    (Set.ncard (G.neighborSet x ∪ G.neighborSet y) : ℝ) =
        ((G.neighborFinset x ∪ G.neighborFinset y).card : ℝ) := by
      exact_mod_cast neighbor_union_ncard_eq_card G x y
    _ ≤ (leafCount Tsub : ℝ) + 2 := by exact_mod_cast hnat'
    _ ≤ Ls G + 2 := by
      simpa [add_comm] using
        (add_le_add_right (leafCount_le_Ls G Tsub hspan hcoetree) 2)

private noncomputable def localMaxSubtype
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    Finset {x // x ∈ G.neighborSet v} :=
  (G.induce (G.neighborSet v)).maximumIndepSet_exists.choose

private lemma localMaxSubtype_isMaximum
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    (G.induce (G.neighborSet v)).IsMaximumIndepSet (localMaxSubtype G v) :=
  (G.induce (G.neighborSet v)).maximumIndepSet_exists.choose_spec

private noncomputable def localMaxSet
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : Finset α :=
  (localMaxSubtype G v).map ⟨Subtype.val, Subtype.val_injective⟩

private lemma localMaxSet_card
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    (localMaxSet G v).card = indepNeighborsCard G v := by
  rw [localMaxSet, card_map]
  exact (G.induce (G.neighborSet v)).maximumIndepSet_card_eq_indepNum
    (localMaxSubtype G v) (localMaxSubtype_isMaximum G v)

private lemma localMaxSet_subset_neighborFinset
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    localMaxSet G v ⊆ G.neighborFinset v := by
  intro u hu
  rw [localMaxSet, mem_map] at hu
  obtain ⟨u', hu', rfl⟩ := hu
  exact (G.mem_neighborFinset v (u' : α)).2 u'.property

private lemma localMaxSet_isIndep
    (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) :
    G.IsIndepSet (localMaxSet G v : Set α) := by
  intro x hx y hy hxy hAdj
  rw [Finset.mem_coe, localMaxSet, Finset.mem_map] at hx hy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have hsub := (localMaxSubtype_isMaximum G v).isIndepSet
  exact hsub (by simpa using hx') (by simpa using hy')
    (by exact Subtype.coe_ne_coe.mp hxy) hAdj

private noncomputable def load
    (G : SimpleGraph α) [DecidableRel G.Adj] (u : α) : ℕ :=
  (Finset.univ.filter fun v => u ∈ localMaxSet G v).card

private lemma sum_load_eq_sum_local (G : SimpleGraph α) [DecidableRel G.Adj] :
    ∑ u, load G u = ∑ v, indepNeighborsCard G v := by
  classical
  simp only [load, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp [localMaxSet_card]

private lemma load_le_degree
    (G : SimpleGraph α) [DecidableRel G.Adj] (u : α) :
    load G u ≤ G.degree u := by
  unfold load
  rw [degree]
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have hvsub := localMaxSet_subset_neighborFinset G v hv
  exact (G.mem_neighborFinset u v).2 ((G.mem_neighborFinset v u).1 hvsub).symm

private lemma localMaxSet_disjoint_neighborFinset_of_mem
    (G : SimpleGraph α) [DecidableRel G.Adj] {v u : α}
    (hu : u ∈ localMaxSet G v) :
    Disjoint (localMaxSet G v) (G.neighborFinset u) := by
  rw [Finset.disjoint_left]
  intro w hwI hwu
  have hind := localMaxSet_isIndep G v
  have hune : u ≠ w := by
    intro h
    subst w
    exact G.irrefl ((G.mem_neighborFinset u u).1 hwu)
  exact hind (by simpa using hu) (by simpa using hwI) hune
    (by simpa [neighborFinset_def] using hwu)

private lemma local_card_add_degree_le_neighbor_union
    (G : SimpleGraph α) [DecidableRel G.Adj] {v u : α}
    (hu : u ∈ localMaxSet G v) :
    indepNeighborsCard G v + G.degree u ≤
      (G.neighborFinset v ∪ G.neighborFinset u).card := by
  have hdis := localMaxSet_disjoint_neighborFinset_of_mem G hu
  have hsub : localMaxSet G v ∪ G.neighborFinset u ⊆
      G.neighborFinset v ∪ G.neighborFinset u := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_union_left _ (localMaxSet_subset_neighborFinset G v hw)
    · exact Finset.mem_union_right _ hw
  calc
    indepNeighborsCard G v + G.degree u =
        (localMaxSet G v).card + (G.neighborFinset u).card := by
      rw [localMaxSet_card, degree]
    _ = (localMaxSet G v ∪ G.neighborFinset u).card := by
      rw [Finset.card_union_of_disjoint hdis]
    _ ≤ (G.neighborFinset v ∪ G.neighborFinset u).card :=
      Finset.card_le_card hsub

private noncomputable def edgePairs
    (G : SimpleGraph α) [DecidableRel G.Adj] : Finset (α × α) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun p => G.Adj p.1 p.2)

private lemma edgePairs_nonempty
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    (edgePairs G).Nonempty := by
  let x : α := Classical.choice (inferInstance : Nonempty α)
  have hdeg : 0 < G.degree x := hG.preconnected.degree_pos_of_nontrivial x
  have hN : (G.neighborFinset x).Nonempty := by
    rw [← Finset.card_pos, ← degree]
    exact hdeg
  obtain ⟨y, hy⟩ := hN
  refine ⟨(x, y), ?_⟩
  simp [edgePairs, (G.mem_neighborFinset x y).1 hy]

private noncomputable def maxNeighborUnion
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) : ℕ :=
  ((edgePairs G).image
    (fun p => (G.neighborFinset p.1 ∪ G.neighborFinset p.2).card)).max'
    ((edgePairs_nonempty G hG).image _)

private lemma neighbor_union_le_max
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    {v u : α} (hvu : G.Adj v u) :
    (G.neighborFinset v ∪ G.neighborFinset u).card ≤ maxNeighborUnion G hG := by
  unfold maxNeighborUnion
  apply Finset.le_max'
  apply Finset.mem_image.mpr
  exact ⟨(v, u), by simp [edgePairs, hvu], rfl⟩

private lemma exists_edge_with_maxNeighborUnion
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ∃ v u, G.Adj v u ∧
      (G.neighborFinset v ∪ G.neighborFinset u).card = maxNeighborUnion G hG := by
  let vals := (edgePairs G).image
    (fun p => (G.neighborFinset p.1 ∪ G.neighborFinset p.2).card)
  have hvals : vals.Nonempty := (edgePairs_nonempty G hG).image _
  have hmem : vals.max' hvals ∈ vals := Finset.max'_mem vals hvals
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hmem
  refine ⟨p.1, p.2, ?_, ?_⟩
  · simpa [edgePairs] using hp
  · change (G.neighborFinset p.1 ∪ G.neighborFinset p.2).card = vals.max' hvals
    exact heq

private noncomputable def incidenceTotal
    (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ v, ∑ u ∈ localMaxSet G v,
    (G.neighborFinset v ∪ G.neighborFinset u).card

private lemma sum_degree_load_eq_double_sum
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    ∑ u, G.degree u * load G u =
      ∑ v, ∑ u ∈ localMaxSet G v, G.degree u := by
  classical
  calc
    ∑ u, G.degree u * load G u =
        ∑ u, ∑ v, if u ∈ localMaxSet G v then G.degree u else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      unfold load
      rw [Nat.mul_comm, Finset.card_eq_sum_ones, Finset.sum_mul]
      simp only [one_mul]
      rw [Finset.sum_filter]
    _ = ∑ v, ∑ u, if u ∈ localMaxSet G v then G.degree u else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ v, ∑ u ∈ localMaxSet G v, G.degree u := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← Finset.sum_filter]
      simp

private lemma sum_local_sq_add_degree_load_le_incidenceTotal
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    (∑ v, (indepNeighborsCard G v)^2) +
        (∑ u, G.degree u * load G u) ≤ incidenceTotal G := by
  classical
  unfold incidenceTotal
  calc
    (∑ v, (indepNeighborsCard G v)^2) + (∑ u, G.degree u * load G u) =
        ∑ v, ∑ u ∈ localMaxSet G v,
          (indepNeighborsCard G v + G.degree u) := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro v hv
        simp [pow_two, localMaxSet_card]
      · exact sum_degree_load_eq_double_sum G
    _ ≤ ∑ v, ∑ u ∈ localMaxSet G v,
        (G.neighborFinset v ∪ G.neighborFinset u).card := by
      gcongr with v hv u hu
      exact local_card_add_degree_le_neighbor_union G hu

private lemma sum_local_sq_add_load_sq_le_incidenceTotal
    (G : SimpleGraph α) [DecidableRel G.Adj] :
    (∑ v, (indepNeighborsCard G v)^2) +
        (∑ u, (load G u)^2) ≤ incidenceTotal G := by
  calc
    (∑ v, (indepNeighborsCard G v)^2) + (∑ u, (load G u)^2) ≤
        (∑ v, (indepNeighborsCard G v)^2) +
          (∑ u, G.degree u * load G u) := by
      gcongr with u
      have hlu := load_le_degree G u
      nlinarith
    _ ≤ incidenceTotal G := sum_local_sq_add_degree_load_le_incidenceTotal G

private lemma incidenceTotal_le_max_mul_sum_local
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    incidenceTotal G ≤ maxNeighborUnion G hG * ∑ v, indepNeighborsCard G v := by
  classical
  unfold incidenceTotal
  calc
    ∑ v, ∑ u ∈ localMaxSet G v,
        (G.neighborFinset v ∪ G.neighborFinset u).card ≤
        ∑ v, ∑ u ∈ localMaxSet G v, maxNeighborUnion G hG := by
      gcongr with v hv u hu
      have hadj : G.Adj v u :=
        (G.mem_neighborFinset v u).1 (localMaxSet_subset_neighborFinset G v hu)
      exact neighbor_union_le_max G hG hadj
    _ = maxNeighborUnion G hG * ∑ v, indepNeighborsCard G v := by
      calc
        ∑ v, ∑ u ∈ localMaxSet G v, maxNeighborUnion G hG =
            ∑ v, (localMaxSet G v).card * maxNeighborUnion G hG := by simp
        _ = ∑ v, indepNeighborsCard G v * maxNeighborUnion G hG := by
          simp [localMaxSet_card]
        _ = (∑ v, indepNeighborsCard G v) * maxNeighborUnion G hG := by
          rw [Finset.sum_mul]
        _ = maxNeighborUnion G hG * ∑ v, indepNeighborsCard G v := by
          exact Nat.mul_comm _ _

private lemma two_mul_sum_local_le_card_mul_max
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    2 * (∑ v, indepNeighborsCard G v) ≤
      Fintype.card α * maxNeighborUnion G hG := by
  let S := ∑ v, indepNeighborsCard G v
  let Q := ∑ v, (indepNeighborsCard G v)^2
  let R := ∑ u, (load G u)^2
  let T := incidenceTotal G
  let M := maxNeighborUnion G hG
  let n := Fintype.card α
  have hcsQ : S^2 ≤ Q * n := by
    dsimp [S, Q, n]
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
      (fun v => indepNeighborsCard G v) (fun _ => (1 : ℕ)))
  have hloadsum : ∑ u, load G u = S := by
    simpa [S] using sum_load_eq_sum_local G
  have hcsR : S^2 ≤ R * n := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
      (fun u => load G u) (fun _ => (1 : ℕ))
    simpa [R, n, hloadsum] using h
  have hlow : Q + R ≤ T := by
    simpa [Q, R, T] using sum_local_sq_add_load_sq_le_incidenceTotal G
  have hupp : T ≤ M * S := by
    simpa [T, M, S] using incidenceTotal_le_max_mul_sum_local G hG
  have hSpos : 0 < S := by
    let v : α := Classical.choice (inferInstance : Nonempty α)
    have hdeg : 0 < G.degree v := hG.preconnected.degree_pos_of_nontrivial v
    have hneigh : (G.neighborFinset v).Nonempty := by
      rw [← Finset.card_pos, ← degree]
      exact hdeg
    obtain ⟨u, hu⟩ := hneigh
    have hone : 1 ≤ indepNeighborsCard G v := by
      let u' : {x // x ∈ G.neighborSet v} := ⟨u, by simpa using hu⟩
      change 1 ≤ (G.induce (G.neighborSet v)).indepNum
      have hs : (G.induce (G.neighborSet v)).IsIndepSet ({u'} : Finset _) := by
        simp [SimpleGraph.IsIndepSet]
      simpa using hs.card_le_indepNum
    dsimp [S]
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨v, Finset.mem_univ v, lt_of_lt_of_le Nat.zero_lt_one hone⟩
  dsimp [S, M, n] at *
  have hsq : 2 * (∑ v, indepNeighborsCard G v)^2 ≤
      Fintype.card α * incidenceTotal G := by
    nlinarith [hcsQ, hcsR, hlow]
  have hprod : 2 * (∑ v, indepNeighborsCard G v)^2 ≤
      Fintype.card α *
        (maxNeighborUnion G hG * ∑ v, indepNeighborsCard G v) := by
    exact hsq.trans (Nat.mul_le_mul_left _ hupp)
  nlinarith

private lemma two_mul_averageIndepNeighbors_le_max
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    2 * averageIndepNeighbors G ≤ (maxNeighborUnion G hG : ℝ) := by
  have hnat := two_mul_sum_local_le_card_mul_max G hG
  have hnpos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  have hcast :
      (2 : ℝ) * (∑ v, (indepNeighborsCard G v : ℝ)) ≤
        (Fintype.card α : ℝ) * (maxNeighborUnion G hG : ℝ) := by
    exact_mod_cast hnat
  change 2 * ((∑ v, (indepNeighborsCard G v : ℝ)) /
    (Fintype.card α : ℝ)) ≤ (maxNeighborUnion G hG : ℝ)
  have hsumcast :
      (∑ v, (indepNeighborsCard G v : ℝ)) =
        ((∑ v, indepNeighborsCard G v : ℕ) : ℝ) := by
    norm_cast
  rw [hsumcast]
  rw [div_le_iff₀ hnpos]
  nlinarith

private lemma two_mul_averageIndepNeighbors_le_adjacent_neighbor_union
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) :
    ∃ x y, G.Adj x y ∧
      2 * averageIndepNeighbors G ≤
        (Set.ncard (G.neighborSet x ∪ G.neighborSet y) : ℝ) := by
  obtain ⟨x, y, hxy, hmax⟩ := exists_edge_with_maxNeighborUnion G hG
  refine ⟨x, y, hxy, ?_⟩
  have havg := two_mul_averageIndepNeighbors_le_max G hG
  have hsetcard :
      Set.ncard (G.neighborSet x ∪ G.neighborSet y) =
        (G.neighborFinset x ∪ G.neighborFinset y).card := by
    simp [Set.ncard_eq_toFinset_card', neighborFinset_def]
  rw [hsetcard, hmax]
  exact havg

/--
WOWII [Conjecture 2](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`Ls(G) ≥ 2 · (l(G) - 1)` where `l(G)` is the average independence number of
the neighbourhoods of the vertices of `G`.
-/
@[category research solved, AMS 5]
theorem conjecture2 (G : SimpleGraph α) (h : G.Connected) :
    2 * (averageIndepNeighbors G - 1) ≤ Ls G := by
  classical
  obtain ⟨x, y, hxy, havg⟩ :=
    two_mul_averageIndepNeighbors_le_adjacent_neighbor_union G h
  have htree := adjacent_neighbor_union_le_Ls_add_two G h hxy
  linarith

#print axioms conjecture2

end WrittenOnTheWallII.GraphConjecture2
