/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.HamiltonianConstruct

/-!
The path-rerouting core of the Bondy--Chvátal argument.  This is a focused
adaptation of Shuhao Song's unmerged Mathlib development at
`c83689ab8f1abfba1f646e65dc8b131fd256b73f`.
-/

namespace SimpleGraph

open Classical Walk Function
open scoped List

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A spanning path can be closed into a Hamiltonian cycle when one forward dart
can be replaced by two cross edges. -/
theorem isHamiltonian_of_spanning_path_reroute
    {u u' v v' : V} {p : G.Walk u u'}
    (hV : Fintype.card V ≥ 3) (hp : p.support ~ Finset.univ.toList)
    (ne : v ≠ u') (vu' : G.Adj v u') (v'u : G.Adj v' u)
    (d : G.Dart) (hd : d ∈ p.darts) (hd₁ : d.fst = v) (hd₂ : d.snd = v') :
    IsHamiltonian G := by
  have hv : v ∈ p.support := by simp [List.Perm.mem_iff hp]
  have not_nil : ¬(p.dropUntil v hv).Nil := dropUntil_not_nil hv ne
  have snd_eq_v' : (p.dropUntil v hv).getVert 1 = v' := by
    rw [← hd₂]
    refine p.next_unique ?_
      (p.darts_dropUntil_subset _ <| (p.dropUntil v hv).firstDart_mem_darts not_nil)
      hd (by simp [hd₁])
    have hs : p.support.Nodup := by
      rw [List.Perm.nodup_iff hp]
      exact Finset.nodup_toList
    exact List.Nodup.sublist (List.dropLast_sublist _) hs
  let q := (p.takeUntil _ hv)
    |>.append vu'.toWalk
    |>.append (p.dropUntil v hv |>.tail |>.reverse.copy rfl snd_eq_v')
    |>.append v'u.toWalk
  suffices q.IsHamiltonianCycle from fun _ => ⟨u, q, this⟩
  apply IsHamiltonianCycle.of_tail_toFinset
  · have hsplit := p.sum_takeUntil_dropUntil_length hv
    have hcard := calc
      p.length + 1 = p.support.length := by simp
      _ = Finset.univ.toList.length := by exact List.Perm.length_eq hp
      _ = Fintype.card V := by simp
    have htail := Walk.length_tail_add_one not_nil
    simp [q, add_assoc]
    omega
  · exact hV
  · simp only [tail_support_append, support_cons, support_nil, List.tail_cons, support_copy,
      support_reverse, List.tails_reverse, List.append_assoc, List.singleton_append,
      List.cons_append, List.toFinset_append, List.toFinset_cons, List.toFinset_reverse,
      List.toFinset_nil, insert_emptyc_eq, Finset.union_insert, Finset.eq_univ_iff_forall,
      Finset.mem_insert, Finset.mem_union, List.mem_toFinset, Finset.mem_singleton,
      Finset.not_mem_empty, false_or, q]
    intro w
    by_contra hw
    simp only [not_or] at hw
    rcases hw with ⟨hw₁, hw₂, hw₃, hw₄⟩
    have mem_tail : w ∈ p.support.tail := by
      have mem : w ∈ p.support := by simp [List.Perm.mem_iff hp]
      rw [Walk.support_eq_cons] at mem
      simp only [List.mem_cons] at mem
      exact mem.resolve_left hw₄
    have not_mem_drop : w ∉ (p.dropUntil v hv).support.tail := by
      have tail_not_nil := support_tail_ne_nil not_nil
      have hlast : (p.dropUntil v hv).support.tail.getLast tail_not_nil = u' := by
        rw [List.getLast_tail, getLast_support]
      rw [← List.dropLast_append_getLast tail_not_nil, hlast]
      rw [List.tail_reverse_eq_reverse_dropLast, List.mem_reverse] at hw₃
      simpa [← support_tail_of_not_nil _ not_nil] using ⟨hw₃, hw₁⟩
    have append : p.support.tail =
        (p.takeUntil v hv).support.tail ++ (p.dropUntil v hv).support.tail := by
      rw [← tail_support_append, take_spec]
    simp only [append, List.mem_append] at mem_tail
    cases' mem_tail with h h
    · exact hw₂ h
    · exact not_mem_drop h

#print axioms SimpleGraph.isHamiltonian_of_spanning_path_reroute

end SimpleGraph
