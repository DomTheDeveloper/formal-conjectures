/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217OrderCertificate
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Lean.Elab.Tactic.Omega

/-!
# The residue-two order bound for WOWII Conjecture 217

The finite symmetric-power certificate is lifted here to arbitrary bounded
Havel--Hakimi sequences. Applied to a graph degree sequence, handshake parity
improves the sequence bound from fifteen to fourteen vertices.
-/

namespace SimpleGraph.C217OrderBound

open Classical
open C217OrderCertificate

/-- A Havel--Hakimi step cannot increase an entry. -/
lemma havelHakimiStep_preserves_bound (s : List ℕ) (k : ℕ)
    (hbound : ∀ x ∈ s, x ≤ k) :
    ∀ x ∈ havelHakimiStep s, x ≤ k := by
  cases s with
  | nil => simp [havelHakimiStep]
  | cons d rest =>
      simp only [havelHakimiStep]
      let p := rest.splitAt d
      have hleft : ∀ x ∈ p.1, x ≤ k := by
        intro x hx
        exact hbound x (by
          apply List.mem_cons_of_mem
          exact List.mem_of_mem_take hx)
      have hright : ∀ x ∈ p.2, x ≤ k := by
        intro x hx
        exact hbound x (by
          apply List.mem_cons_of_mem
          exact List.mem_of_mem_drop hx)
      intro x hx
      have hx' : x ∈ p.1.map (· - 1) ++ p.2 := by
        simpa using ((List.mergeSort_perm _ _).mem_iff.mp hx)
      rw [List.mem_append] at hx'
      rcases hx' with hx' | hx'
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx'
        exact (Nat.sub_le y 1).trans (hleft y hy)
      · exact hright x hx'

/-- Every Havel--Hakimi step is returned in descending order. -/
lemma havelHakimiStep_pairwise_ge (s : List ℕ) :
    (havelHakimiStep s).Pairwise (· ≥ ·) := by
  cases s with
  | nil => simp [havelHakimiStep]
  | cons d rest =>
      simp only [havelHakimiStep]
      exact List.pairwise_mergeSort' _ _

/-- A bounded descending sequence of Havel--Hakimi residue two has at most
fifteen entries. -/
theorem length_le_fifteen_of_residueAux_eq_two (s : List ℕ)
    (hbound : ∀ x ∈ s, x ≤ 6) (hsorted : s.Pairwise (· ≥ ·))
    (hres : residueAux s = 2) :
    s.length ≤ 15 := by
  by_cases hsmall : s.length ≤ 15
  · exact hsmall
  cases s with
  | nil => simp at hsmall
  | cons d rest =>
      cases d with
      | zero =>
          simp [residueAux] at hres
          omega
      | succ d =>
          let t := havelHakimiStep ((d + 1) :: rest)
          have htres : residueAux t = 2 := by
            simpa [residueAux, t] using hres
          have htbound : ∀ x ∈ t, x ≤ 6 := by
            exact havelHakimiStep_preserves_bound ((d + 1) :: rest) 6 hbound
          have htsorted : t.Pairwise (· ≥ ·) := havelHakimiStep_pairwise_ge _
          have htlen : t.length = rest.length := by
            simpa [t] using havelHakimiStep_length_cons (d + 1) rest
          have ht : t.length ≤ 15 :=
            length_le_fifteen_of_residueAux_eq_two t htbound htsorted htres
          have hle16 : ((d + 1) :: rest).length ≤ 16 := by
            simp only [List.length_cons]
            rw [htlen] at ht
            omega
          have hne16 : ((d + 1) :: rest).length ≠ 16 := by
            intro hlen
            let m : Sym (Fin 7) 16 :=
              Sym.mk (((((d + 1) :: rest).map cappedFin7 : List (Fin 7)) :
                Multiset (Fin 7))) (by simp [hlen])
            have heq : degreeList m = (d + 1) :: rest := by
              have hrec := degreeList_cappedSym_eq ((d + 1) :: rest) hbound hsorted
              simpa [m, cappedSym, hlen] using hrec
            exact no_residue_two_length_sixteen_finite m (by simpa [heq] using hres)
          omega
termination_by s.length

decreasing_by
  simpa [t] using havelHakimiStep_length_cons (d + 1) rest

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The descending degree sequence used by the repository definition of residue. -/
noncomputable def degreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v => G.degree v).sort (· ≥ ·)

@[simp] lemma degreeSequence_length (G : SimpleGraph α) [DecidableRel G.Adj] :
    (degreeSequence G).length = Fintype.card α := by
  simp [degreeSequence]

lemma degreeSequence_pairwise (G : SimpleGraph α) [DecidableRel G.Adj] :
    (degreeSequence G).Pairwise (· ≥ ·) := by
  exact Multiset.pairwise_sort _ _

lemma degreeSequence_bound (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ)
    (hdeg : ∀ v, G.degree v ≤ k) :
    ∀ d ∈ degreeSequence G, d ≤ k := by
  intro d hd
  have hd' : d ∈ Finset.univ.val.map (fun v => G.degree v) := by
    simpa [degreeSequence] using hd
  obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hd'
  exact hdeg v

lemma degreeSequence_sum (G : SimpleGraph α) [DecidableRel G.Adj] :
    (degreeSequence G).sum = ∑ v, G.degree v := by
  unfold degreeSequence
  rw [← Multiset.sum_coe, Multiset.sort_eq]
  simp

/-- In the C217 exceptional branch, residue two and maximum degree six force
at most fourteen vertices. -/
theorem card_le_fourteen_of_residue_eq_two_of_degree_le_six
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hres : residue G = 2) (hdeg : ∀ v, G.degree v ≤ 6) :
    Fintype.card α ≤ 14 := by
  let s := degreeSequence G
  have hsres : residueAux s = 2 := by
    simpa [s, degreeSequence, residue] using hres
  have hsbound : ∀ d ∈ s, d ≤ 6 := degreeSequence_bound G 6 hdeg
  have hssorted : s.Pairwise (· ≥ ·) := degreeSequence_pairwise G
  have hle15 : s.length ≤ 15 :=
    length_le_fifteen_of_residueAux_eq_two s hsbound hssorted hsres
  rw [degreeSequence_length] at hle15
  by_contra hnot
  have hcard : Fintype.card α = 15 := by omega
  have hslen : s.length = 15 := by simp [s, hcard]
  let m : Sym (Fin 7) 15 :=
    Sym.mk (((s.map cappedFin7 : List (Fin 7)) : Multiset (Fin 7))) (by simp [hslen])
  have heq : degreeList m = s := by
    have hrec := degreeList_cappedSym_eq s hsbound hssorted
    simpa [m, cappedSym, hslen] using hrec
  have hodd : s.sum % 2 = 1 := by
    have hm := residue_two_length_fifteen_has_odd_sum_finite m
    simpa [heq, hsres] using hm hsres
  have heven : s.sum % 2 = 0 := by
    rw [degreeSequence_sum, G.sum_degrees_eq_twice_card_edges]
    omega
  omega

#print axioms SimpleGraph.C217OrderBound.length_le_fifteen_of_residueAux_eq_two
#print axioms SimpleGraph.C217OrderBound.card_le_fourteen_of_residue_eq_two_of_degree_le_six

end SimpleGraph.C217OrderBound
