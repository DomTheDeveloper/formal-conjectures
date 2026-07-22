/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
A support-count constructor for Hamiltonian cycles, used by the source-level
Bondy--Chvátal rerouting proof. Adapted from Shuhao Song's unmerged Mathlib
branch at `c83689ab8f1abfba1f646e65dc8b131fd256b73f`.
-/

open Finset Function

namespace SimpleGraph

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}
  {a : α} {p : G.Walk a a}

namespace Walk.IsHamiltonianCycle

open scoped List

private theorem of_support_count
    (hp : p.length ≥ 3) (hp' : ∀ x : α, List.count x p.support.tail = 1) :
    p.IsHamiltonianCycle := by
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one]
  rw [Walk.isCycle_def, Walk.isTrail_def]
  refine And.intro ?_ hp'
  apply And.intro
  · rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hij
    unfold Walk.edges
    have nodup : p.support.tail.Nodup := by
      rw [List.nodup_iff_count_le_one]
      exact fun x => le_of_eq (hp' x)
    rw [List.Nodup, List.pairwise_iff_getElem] at nodup
    have h₁ : i < p.length := by simpa using hi
    have h₂ : j < p.length := by simpa using hj
    have h₅ : i < p.support.tail.length := by simpa using hi
    have h₆ : j < p.support.tail.length := by simpa using hj
    simp only [length_edges] at hi
    simp only [List.getElem_map, ne_eq, dart_edge_eq_iff, not_or]
    apply And.intro
    · have h₇ := p.darts_getElem_snd_eq_support_tail i h₁
      have h₈ := p.darts_getElem_snd_eq_support_tail j h₂
      suffices p.darts[i].snd ≠ p.darts[j].snd by
        contrapose this
        simp at this ⊢
        congr
      simp only [h₇, h₈]
      exact nodup i j h₅ h₆ hij
    · intro h
      by_cases ij : i + 1 < j
      · apply_fun (·.snd) at h
        simp only [Dart.symm_toProd, Prod.snd_swap] at h
        rw [p.darts_getElem_snd_eq_support_tail i h₁,
          p.darts_getElem_fst_eq_support_tail j (by omega)] at h
        exact nodup i (j - 1) h₅ (by omega) (by omega) h
      · apply_fun (·.fst) at h
        by_cases i0 : i = 0
        · simp only [i0, List.getElem_zero,
            p.head_darts_fst (by apply List.ne_nil_of_length_pos; simp; omega)] at h
          have hlast : p.support.tail[p.length - 1]'(by simp; omega) = a := by
            simp [List.getElem_tail, show p.length - 1 + 1 = p.length by omega,
              support_getElem_eq_getVert]
          simp only [← hlast, Dart.symm_toProd, Prod.fst_swap,
            p.darts_getElem_snd_eq_support_tail j h₂] at h
          exact nodup j (p.length - 1) h₆ (by simp; omega) (by omega) h.symm
        · simp only [p.darts_getElem_fst_eq_support_tail i (by omega),
            p.darts_getElem_snd_eq_support_tail j h₂, Dart.symm_toProd, Prod.fst_swap] at h
          exact nodup (i - 1) j (by omega) h₆ (by omega) h
  · apply And.intro
    · intro nil_p
      apply_fun (·.length) at nil_p
      simp only [Walk.length_nil] at nil_p
      omega
    · rw [List.nodup_iff_count_le_one]
      exact fun x => le_of_eq (hp' x)

/-- A closed walk of full length whose tail support contains every vertex is a
Hamiltonian cycle. -/
theorem of_tail_toFinset [Fintype α]
    (hp : p.length = Fintype.card α)
    (hα : Fintype.card α ≥ 3) (hp' : p.support.tail.toFinset = Finset.univ) :
    p.IsHamiltonianCycle := by
  apply of_support_count
  · rwa [hp]
  suffices p.support.tail ~ Finset.univ.toList by
    intro x
    rw [List.Perm.count_eq this]
    apply List.count_eq_one_of_mem
    · apply Finset.nodup_toList
    · simp
  apply List.Perm.symm
  apply List.Subperm.perm_of_length_le
  · rw [List.subperm_ext_iff]
    intro x hx
    rw [List.count_eq_one_of_mem (Finset.nodup_toList _) hx]
    rw [Nat.succ_le, List.count_pos_iff]
    rwa [Finset.mem_toList, ← hp', List.mem_toFinset] at hx
  · simp [hp]

#print axioms SimpleGraph.Walk.IsHamiltonianCycle.of_tail_toFinset

end Walk.IsHamiltonianCycle
end SimpleGraph
