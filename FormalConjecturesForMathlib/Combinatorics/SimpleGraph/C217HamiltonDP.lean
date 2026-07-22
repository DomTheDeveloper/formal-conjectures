/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.ConeHamiltonian
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# A finite Boolean Hamilton-path dynamic program

`pathStart G k S v` searches for a simple path that starts at `v`, visits
exactly the vertices of `S`, and has `k` edges.  The recursion removes the
current initial vertex, so its soundness proof simultaneously constructs a
nodup support list.  This layer contains no trusted computation: later finite
certificates only need to prove that `hasHamiltonPathBool G = true`.
-/

namespace SimpleGraph.C217HamiltonDP

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Subset dynamic program for a simple path starting at `v` and covering `S`. -/
def pathStart (G : SimpleGraph V) [DecidableRel G.Adj] :
    ℕ → Finset V → V → Bool
  | 0, S, v => decide (S = {v})
  | k + 1, S, v =>
      decide (v ∈ S) &&
        (S.erase v).any fun w => decide (G.Adj v w) && pathStart G k (S.erase v) w

/-- The Hamilton-path Boolean searches over the initial vertex. -/
def hasHamiltonPathBool (G : SimpleGraph V) [DecidableRel G.Adj] : Bool :=
  Finset.univ.any fun v => pathStart G (Fintype.card V - 1) Finset.univ v

/-- Soundness of the subset DP.  A successful state produces a nodup support
list beginning at the requested vertex and covering exactly the requested
finset. -/
theorem pathStart_sound (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ k S v, pathStart G k S v = true →
      ∃ t : List V,
        (v :: t).Nodup ∧
        (v :: t).toFinset = S ∧
        (v :: t).IsChain G.Adj := by
  intro k
  induction k with
  | zero =>
      intro S v h
      have hS : S = {v} := by
        simpa [pathStart] using h
      refine ⟨[], ?_, ?_, ?_⟩
      · simp
      · simp [hS]
      · exact .singleton v
  | succ k ih =>
      intro S v h
      have hsplit :
          v ∈ S ∧
            (S.erase v).any (fun w =>
              decide (G.Adj v w) && pathStart G k (S.erase v) w) = true := by
        simpa [pathStart, Bool.and_eq_true] using h
      have hv : v ∈ S := hsplit.1
      have hex : ∃ w ∈ S.erase v,
          G.Adj v w ∧ pathStart G k (S.erase v) w = true := by
        simpa [Finset.any_eq_true, Bool.and_eq_true] using hsplit.2
      obtain ⟨w, hw, hadj, hrec⟩ := hex
      obtain ⟨t, hnodup, hfin, hchain⟩ := ih (S.erase v) w hrec
      refine ⟨w :: t, ?_, ?_, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨?_, hnodup⟩
        intro hmem
        have hvErase : v ∈ S.erase v := by
          rw [← hfin]
          exact List.mem_toFinset.mpr hmem
        exact (Finset.notMem_erase v S) hvErase
      · simp only [List.toFinset_cons, hfin]
        exact Finset.insert_erase hv
      · exact .cons_cons hadj hchain

/-- A successful Boolean search gives a Mathlib Hamiltonian walk. -/
theorem isTraceable_of_hasHamiltonPathBool
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : hasHamiltonPathBool G = true) : IsTraceable G := by
  have hex : ∃ v ∈ (Finset.univ : Finset V),
      pathStart G (Fintype.card V - 1) Finset.univ v = true := by
    simpa [hasHamiltonPathBool, Finset.any_eq_true] using h
  obtain ⟨v, _, hv⟩ := hex
  obtain ⟨t, hnodup, hfin, hchain⟩ :=
    pathStart_sound G (Fintype.card V - 1) Finset.univ v hv
  let l : List V := v :: t
  have hlne : l ≠ [] := by simp [l]
  let p : G.Walk (l.head hlne) (l.getLast hlne) := Walk.ofSupport l hlne hchain
  refine ⟨l.head hlne, l.getLast hlne, p, ?_⟩
  have hpPath : p.IsPath := by
    apply Walk.IsPath.mk'
    simpa [p, l] using hnodup
  apply hpPath.isHamiltonian_of_mem
  intro x
  have hxFin : x ∈ l.toFinset := by
    rw [show l.toFinset = Finset.univ by simpa [l] using hfin]
    exact Finset.mem_univ x
  have hxList : x ∈ l := List.mem_toFinset.mp hxFin
  simpa [p, l] using hxList

#print axioms SimpleGraph.C217HamiltonDP.pathStart_sound
#print axioms SimpleGraph.C217HamiltonDP.isTraceable_of_hasHamiltonPathBool

end SimpleGraph.C217HamiltonDP
