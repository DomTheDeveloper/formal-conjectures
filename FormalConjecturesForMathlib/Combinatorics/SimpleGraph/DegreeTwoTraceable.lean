/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Lean.Elab.Tactic.Omega

open Classical
namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- In a connected graph, every nontrivial vertex cut has a crossing edge. -/
private lemma exists_adj_crossing
    (G : SimpleGraph α) (hG : G.Connected) (S : Set α)
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    ∃ u, u ∈ S ∧ ∃ v, v ∉ S ∧ G.Adj u v := by
  rcases hS with ⟨u, hu⟩
  rcases hSc with ⟨v, hv⟩
  by_contra hn
  push_neg at hn
  let H : G.Subgraph := (⊤ : G.Subgraph).induce S
  have hvH : v ∈ H.verts :=
    (hG u v).mem_subgraphVerts (H := H) (by
      intro x hx y hxy
      have hxS : x ∈ S := by simpa [H] using hx
      have hyS : y ∈ S := by
        by_contra hyS
        exact hn x hxS y hyS hxy
      simpa [H, hxS, hyS] using hxy) (by
        simpa [H] using hu)
  exact hv (by simpa [H] using hvH)

private lemma maximalPath_endpoint_no_external_neighbor
    (G : SimpleGraph α) {a b : α} {p : G.Walk a b}
    (hp : p.IsPath)
    (hmax : ∀ (u v : α) (q : G.Walk u v), q.IsPath → q.length ≤ p.length) :
    (∀ x, G.Adj x a → x ∈ p.support) ∧
      (∀ x, G.Adj b x → x ∈ p.support) := by
  constructor
  · intro x hxa
    by_contra hxout
    have hnew : (p.cons hxa).IsPath := hp.cons hxout
    have hle := hmax x b (p.cons hxa) hnew
    simp at hle
  · intro x hbx
    by_contra hxout
    have hxrev : x ∉ p.reverse.support := by simpa using hxout
    have hnew : (p.reverse.cons hbx.symm).IsPath := hp.reverse.cons hxrev
    have hle := hmax x a (p.reverse.cons hbx.symm) hnew
    simp at hle

private lemma three_le_degree_of_path_internal_and_external
    (G : SimpleGraph α) [DecidableRel G.Adj] {a b u v : α} {p : G.Walk a b}
    (hp : p.IsPath) (hu : u ∈ p.support) (hua : u ≠ a) (hub : u ≠ b)
    (hvout : v ∉ p.support) (huv : G.Adj u v) :
    3 ≤ G.degree u := by
  obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.mp hu
  have hi0 : i ≠ 0 := by
    intro h
    subst i
    simp at hi
    exact hua hi.symm
  have hilast : i ≠ p.length := by
    intro h
    subst i
    rw [p.getVert_length] at hi
    exact hub hi.symm
  have hilt : i < p.length := lt_of_le_of_ne hile hilast
  have hinter : (p.toSubgraph.neighborSet u).ncard = 2 := by
    rw [← hi]
    exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
  have hvnot : v ∉ p.toSubgraph.neighborSet u := by
    intro hv
    have hvverts : v ∈ p.toSubgraph.verts := p.toSubgraph.neighborSet_subset_verts u hv
    exact hvout (by simpa using hvverts)
  let N : Finset α := (p.toSubgraph.neighborSet u).toFinset
  have hvnotN : v ∉ N := by simpa [N] using hvnot
  have hNcard : N.card = 2 := by
    change (p.toSubgraph.neighborSet u).toFinset.card = 2
    rw [← Set.ncard_eq_toFinset_card']
    exact hinter
  have hsub : insert v N ⊆ G.neighborFinset u := by
    intro x hx
    simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hx ⊢
    rcases hx with rfl | hx
    · exact huv
    · exact p.toSubgraph.neighborSet_subset u (by simpa [N] using hx)
  have hcard : (insert v N).card = 3 := by
    rw [Finset.card_insert_of_notMem hvnotN, hNcard]
  have hle := Finset.card_le_card hsub
  rw [hcard, card_neighborFinset_eq_degree] at hle
  exact hle

/-- A finite connected graph of maximum degree at most two has a Hamiltonian path. -/
theorem Connected.exists_hamiltonianPath_of_degree_le_two
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hdeg : ∀ v, G.degree v ≤ 2) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a, b, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨a, b, p, ?_⟩
  apply hp.isHamiltonian_of_mem
  intro x
  by_contra hx
  let S : Set α := {y | y ∈ p.support}
  have hS : S.Nonempty := ⟨a, by simp [S]⟩
  have hSc : Sᶜ.Nonempty := ⟨x, by simpa [S] using hx⟩
  obtain ⟨u, huS, v, hvS, huv⟩ := exists_adj_crossing G hG S hS hSc
  have hu : u ∈ p.support := by simpa [S] using huS
  have hv : v ∉ p.support := by simpa [S] using hvS
  obtain ⟨hstart, hend⟩ := maximalPath_endpoint_no_external_neighbor G hp hmax
  have hua : u ≠ a := by
    intro h
    subst u
    exact hv (hstart v huv.symm)
  have hub : u ≠ b := by
    intro h
    subst u
    exact hv (hend v huv)
  have hthree : 3 ≤ G.degree u :=
    three_le_degree_of_path_internal_and_external G hp hu hua hub hv huv
  have htwo : G.degree u ≤ 2 := hdeg u
  omega

#print axioms SimpleGraph.Connected.exists_hamiltonianPath_of_degree_le_two

end SimpleGraph
