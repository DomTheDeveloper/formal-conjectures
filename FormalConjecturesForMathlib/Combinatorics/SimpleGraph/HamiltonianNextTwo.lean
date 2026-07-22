/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.HamiltonianNext

/-!
Rotation and two-step successor facts for the source-level Bondy--Chvátal proof.
Adapted from Shuhao Song's unmerged Mathlib branch at
`c83689ab8f1abfba1f646e65dc8b131fd256b73f`.
-/

namespace SimpleGraph

variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}
  {a b : α} {p : G.Walk a a}

namespace Walk.IsHamiltonianCycle

/-- Rotate a Hamiltonian cycle so that it starts at the chosen vertex. -/
def rotateAt (hp : p.IsHamiltonianCycle) (b : α) :
    (p.rotate b (hp.mem_support b)).IsHamiltonianCycle :=
  hp.rotate (hp.mem_support b)

lemma rotateAt_next (hp : p.IsHamiltonianCycle) (b' : α) :
    (hp.rotateAt b').next b = hp.next b := by
  unfold rotateAt IsHamiltonianCycle.next dartWithFst
  congr
  ext d
  apply Iff.and
  rw [List.IsRotated.mem_iff (p.rotate_darts _)]
  exact Iff.rfl

lemma support_getElem_succ (hp : p.IsHamiltonianCycle)
    {i : ℕ} (hi : i < p.length) (hi' : p.support[i]'(by simp; omega) = b) :
    p.support[i + 1]'(by simp; omega) = hp.next b := by
  have mem := List.getElem_mem p.darts i (by simpa)
  obtain ⟨d, mem', hd₂, hd₃⟩ := hp.self_next_in_darts b
  rw [← hi', ← p.darts_getElem_fst i hi] at hd₂
  rw [← p.darts_getElem_snd i hi, ← hd₃]
  exact hp.isCycle.next_unique mem mem' hd₂.symm

theorem next_next_ne (hp : p.IsHamiltonianCycle) : hp.next (hp.next b) ≠ b := by
  have mem : b ∈ p.support := hp.mem_support b
  let p' := p.rotate b mem
  have hp' : p'.IsHamiltonianCycle := hp.rotateAt b
  have len_ge_3 := hp'.isCycle.three_le_length
  have p'_at_0 : p'.support[0] = b := by simp [List.getElem_zero]
  have p'_at_1 : p'.support[1]'(by simp; omega) = hp'.next b :=
    hp'.support_getElem_succ (i := 0) (by omega) p'_at_0
  have p'_at_2 : p'.support[2]'(by simp; omega) = hp'.next (hp'.next b) :=
    hp'.support_getElem_succ (i := 1) (by omega) p'_at_1
  simp only [← hp.rotateAt_next b b]
  intro h
  change hp'.next (hp'.next b) = b at h
  simp_rw [← p'_at_2, ← p'_at_0] at h
  rw [← List.getElem_dropLast _ 2 (by simp; omega)] at h
  rw [← List.getElem_dropLast _ 0 (by simp; omega)] at h
  rw [List.Nodup.getElem_inj_iff hp'.support_dropLast_Nodup] at h
  simp at h

#print axioms SimpleGraph.Walk.IsHamiltonianCycle.rotateAt_next
#print axioms SimpleGraph.Walk.IsHamiltonianCycle.next_next_ne

end Walk.IsHamiltonianCycle
end SimpleGraph
