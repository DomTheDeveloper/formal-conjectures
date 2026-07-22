/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
A minimal compatibility layer for the source-level Bondy--Chvátal proof.
Adapted from Shuhao Song's unmerged Mathlib branch at
`c83689ab8f1abfba1f646e65dc8b131fd256b73f`.
-/

open Finset Function

namespace SimpleGraph

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}
  {a b : α} {p : G.Walk a b}

namespace Walk.IsHamiltonianCycle

open scoped List

protected theorem transfer (hp : p.IsHamiltonianCycle) {H : SimpleGraph α}
    (h : ∀ e ∈ p.edges, e ∈ H.edgeSet) :
    (p.transfer H h).IsHamiltonianCycle := by
  rw [isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at *
  refine And.intro (hp.1.transfer _) (fun x => ?_)
  simp only [support_transfer]
  exact hp.2 x

variable (b)

lemma mem_tail_support (hp : p.IsHamiltonianCycle) : b ∈ p.support.tail := by
  rw [← List.count_pos_iff]
  have hcount := hp.2 b
  rw [← Walk.support_tail_of_not_nil p hp.not_nil]
  omega

lemma mem_dropLast_support (hp : p.IsHamiltonianCycle) : b ∈ p.support.dropLast := by
  rw [List.IsRotated.mem_iff (IsRotated_dropLast_tail p)]
  exact hp.mem_tail_support b

/-- The dart in a Hamiltonian cycle that starts at `b`. -/
noncomputable def dartWithFst (hp : p.IsHamiltonianCycle) : G.Dart :=
  Exists.choose <| show ∃ d ∈ p.darts, d.fst = b by
    simpa [← Walk.map_fst_darts] using hp.mem_dropLast_support b

/-- The dart in a Hamiltonian cycle that ends at `b`. -/
noncomputable def dartWithSnd (hp : p.IsHamiltonianCycle) : G.Dart :=
  Exists.choose <| show ∃ d ∈ p.darts, d.snd = b by
    simpa [← Walk.map_snd_darts] using hp.mem_tail_support b

/-- The next vertex in a Hamiltonian cycle. -/
protected noncomputable def next (hp : p.IsHamiltonianCycle) : α :=
  (hp.dartWithFst b).snd

/-- The previous vertex in a Hamiltonian cycle. -/
protected noncomputable def prev (hp : p.IsHamiltonianCycle) : α :=
  (hp.dartWithSnd b).fst

lemma prev_self_in_darts (hp : p.IsHamiltonianCycle) :
    ∃ d ∈ p.darts, d.fst = hp.prev b ∧ d.snd = b := by
  unfold IsHamiltonianCycle.prev dartWithSnd
  generalize_proofs hd
  have hspec := hd.choose_spec
  set d := hd.choose
  use d
  simpa using hspec

lemma self_next_in_darts (hp : p.IsHamiltonianCycle) :
    ∃ d ∈ p.darts, d.fst = b ∧ d.snd = hp.next b := by
  unfold IsHamiltonianCycle.next dartWithFst
  generalize_proofs hd
  have hspec := hd.choose_spec
  set d := hd.choose
  use d
  simpa using hspec

lemma adj_prev_left (hp : p.IsHamiltonianCycle) : G.Adj (hp.prev b) b := by
  obtain ⟨d, _, hd⟩ := hp.prev_self_in_darts b
  exact hd.1 ▸ hd.2 ▸ d.adj

lemma adj_self_next (hp : p.IsHamiltonianCycle) : G.Adj b (hp.next b) := by
  obtain ⟨d, _, hd⟩ := hp.self_next_in_darts b
  exact hd.2 ▸ hd.1 ▸ d.adj

@[simp] lemma prev_next (hp : p.IsHamiltonianCycle) : hp.prev (hp.next b) = b := by
  obtain ⟨d₁, hd₁, hd₁'⟩ := hp.prev_self_in_darts (hp.next b)
  obtain ⟨d₂, hd₂, hd₂'⟩ := hp.self_next_in_darts b
  rw [← hd₁'.1, ← hd₂'.1]
  rw [← hd₂'.2] at hd₁'
  exact hp.1.prev_unique hd₁ hd₂ hd₁'.2

@[simp] lemma next_prev (hp : p.IsHamiltonianCycle) : hp.next (hp.prev b) = b := by
  obtain ⟨d₁, hd₁, hd₁'⟩ := hp.self_next_in_darts (hp.prev b)
  obtain ⟨d₂, hd₂, hd₂'⟩ := hp.prev_self_in_darts b
  rw [← hd₁'.2, ← hd₂'.2]
  rw [← hd₂'.1] at hd₁'
  exact hp.1.next_unique hd₁ hd₂ hd₁'.1

lemma next_inj (hp : p.IsHamiltonianCycle) : Function.Injective hp.next := by
  intro v₁ v₂ h
  apply_fun hp.prev at h
  simpa using h

variable {b}

lemma next_ne (hp : p.IsHamiltonianCycle) : hp.next b ≠ b := by
  intro h
  exact G.irrefl (h ▸ hp.adj_self_next b)

#print axioms SimpleGraph.Walk.IsHamiltonianCycle.transfer
#print axioms SimpleGraph.Walk.IsHamiltonianCycle.next_inj
#print axioms SimpleGraph.Walk.IsHamiltonianCycle.next_ne

end Walk.IsHamiltonianCycle
end SimpleGraph
