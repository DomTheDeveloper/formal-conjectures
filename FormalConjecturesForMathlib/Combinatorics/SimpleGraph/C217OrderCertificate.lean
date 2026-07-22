/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Residue
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Card
import Lean.Elab.Tactic.Omega

/-!
# Kernel-computable order certificate for WOWII Conjecture 217

A symmetric power `Sym (Fin 7) n` is exactly a multiset of `n` entries from
`0, ..., 6`. Sorting that multiset gives every descending degree list bounded
by six, with no completeness lemma for a hand-written list generator required.

The two finite kernel checks prove:

* no descending bounded list of length sixteen has Havel--Hakimi residue two;
* every descending bounded list of length fifteen with residue two has odd sum.

The graph-theoretic bridge then uses the handshake parity law.
-/

namespace SimpleGraph.C217OrderCertificate

/-- Turn a bounded multiset into its descending natural-number list. -/
def degreeList {n : ℕ} (m : Sym (Fin 7) n) : List ℕ :=
  ((m : Multiset (Fin 7)).map fun x => x.val).sort (· ≥ ·)

/-- Cap a natural number at six and regard it as an element of `Fin 7`. -/
def cappedFin7 (x : ℕ) : Fin 7 :=
  ⟨min x 6, by omega⟩

/-- The symmetric-power representative associated with a list after capping. -/
def cappedSym (s : List ℕ) : Sym (Fin 7) s.length :=
  Sym.mk (((s.map cappedFin7 : List (Fin 7)) : Multiset (Fin 7))) (by simp)

lemma map_cappedFin7_val_eq_self (s : List ℕ)
    (hbound : ∀ x ∈ s, x ≤ 6) :
    s.map (fun x => (cappedFin7 x).val) = s := by
  induction s with
  | nil => rfl
  | cons a s ih =>
      have ha : a ≤ 6 := hbound a (by simp)
      have hs : ∀ x ∈ s, x ≤ 6 := by
        intro x hx
        exact hbound x (by simp [hx])
      simp [cappedFin7, Nat.min_eq_left ha, ih hs]

/-- Every descending bounded list is recovered exactly from its symmetric-power
representative. This is the completeness bridge for the finite certificate. -/
theorem degreeList_cappedSym_eq (s : List ℕ)
    (hbound : ∀ x ∈ s, x ≤ 6) (hsorted : s.Pairwise (· ≥ ·)) :
    degreeList (cappedSym s) = s := by
  unfold degreeList cappedSym
  simp only [Sym.coe_mk, Multiset.map_coe, List.map_map, Function.comp_apply]
  rw [map_cappedFin7_val_eq_self s hbound]
  have hp : ((s : Multiset ℕ).sort (· ≥ ·)) ~ s := by
    rw [← Multiset.coe_eq_coe]
    simp
  exact hp.eq_of_pairwise' (Multiset.pairwise_sort _ _) hsorted

/-- Exhaustive kernel check over all `C(22,6)=74613` bounded multisets of
length sixteen. -/
theorem no_residue_two_length_sixteen_finite :
    ∀ m : Sym (Fin 7) 16, residueAux (degreeList m) ≠ 2 := by
  decide

/-- Exhaustive kernel check over all `C(21,6)=54264` bounded multisets of
length fifteen. -/
theorem residue_two_length_fifteen_has_odd_sum_finite :
    ∀ m : Sym (Fin 7) 15,
      residueAux (degreeList m) = 2 → (degreeList m).sum % 2 = 1 := by
  decide

#print axioms SimpleGraph.C217OrderCertificate.degreeList_cappedSym_eq
#print axioms SimpleGraph.C217OrderCertificate.no_residue_two_length_sixteen_finite
#print axioms SimpleGraph.C217OrderCertificate.residue_two_length_fifteen_has_odd_sum_finite

end SimpleGraph.C217OrderCertificate
