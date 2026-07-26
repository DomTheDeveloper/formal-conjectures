/-
Copyright 2026 The Formal Conjectures Authors.

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

import Mathlib.Data.Nat.ChineseRemainder

/-!
# A CRT obstruction for Erdős Problem 7

A finite collection of congruence classes with pairwise-coprime moduli greater
than one cannot cover all natural numbers. Indeed, prescribe the residue
`a i + 1` modulo each `m i` and apply the Chinese remainder theorem. The
resulting integer avoids every original class `a i (mod m i)`.

Consequently, every candidate strict odd covering system for Erdős Problem 7
must contain two moduli with a nontrivial common factor. This is a structural
pruning rule, not a solution of the full problem.
-/

namespace Erdos7

open scoped Function

/-- Pairwise-coprime nontrivial moduli cannot support a finite congruence cover. -/
theorem pairwise_coprime_residue_classes_do_not_cover
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a m : ι → ℕ)
    (hm : ∀ i, 1 < m i)
    (hcop : Pairwise (Nat.Coprime on m)) :
    ∃ x : ℕ, ∀ i, ¬ x ≡ a i [MOD m i] := by
  let t : Finset ι := Finset.univ
  have hm0 : ∀ i ∈ t, m i ≠ 0 := by
    intro i _
    omega
  have hpair : Set.Pairwise (↑t : Set ι) (Nat.Coprime on m) := by
    intro i _ j _ hij
    exact hcop hij
  let x := Nat.chineseRemainderOfFinset (fun i => a i + 1) m t hm0 hpair
  refine ⟨x, ?_⟩
  intro i hxi
  have htarget : (x : ℕ) ≡ a i + 1 [MOD m i] :=
    x.property i (Finset.mem_univ i)
  have hnext : a i + 1 ≡ a i [MOD m i] := htarget.symm.trans hxi
  have h10 : 1 ≡ 0 [MOD m i] := by
    apply Nat.ModEq.add_left_cancel' (a i)
    simpa using hnext
  have hd : m i ∣ 1 := Nat.modEq_zero_iff_dvd.mp h10
  have hmle : m i ≤ 1 := Nat.le_of_dvd (by norm_num) hd
  omega

/-- Any finite congruence cover with all moduli greater than one contains two
non-coprime moduli. -/
theorem exists_non_coprime_moduli_of_cover
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a m : ι → ℕ)
    (hm : ∀ i, 1 < m i)
    (hcover : ∀ x : ℕ, ∃ i, x ≡ a i [MOD m i]) :
    ∃ i j, i ≠ j ∧ ¬ Nat.Coprime (m i) (m j) := by
  by_contra h
  push_neg at h
  have hcop : Pairwise (Nat.Coprime on m) := by
    intro i j hij
    exact h i j hij
  obtain ⟨x, hx⟩ := pairwise_coprime_residue_classes_do_not_cover a m hm hcop
  obtain ⟨i, hi⟩ := hcover x
  exact hx i hi

#print axioms pairwise_coprime_residue_classes_do_not_cover
#print axioms exists_non_coprime_moduli_of_cover

end Erdos7
