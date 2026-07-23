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

import FormalConjectures.Other.LittMostUnfairBetDefs
import Mathlib.Data.Fin.Rev

/-!
# Reversal symmetry of proper self-overlaps
-/

set_option autoImplicit false

namespace LittMostUnfairBet

/-- Reverse a finite binary word. -/
def reverseWord {n : ℕ} (A : Word n) : Word n := fun i => A i.rev

@[simp] theorem reverseWord_reverseWord {n : ℕ} (A : Word n) :
    reverseWord (reverseWord A) = A := by
  funext i
  simp [reverseWord]

/-- Reversal swaps the prefix and suffix blocks of every fixed length. -/
theorem reverse_self_overlap_iff {n : ℕ} (A : Word n) (k : Fin n) :
    wordSuffix (reverseWord A) k = wordPrefix (reverseWord A) k ↔
      wordSuffix A k = wordPrefix A k := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i.rev
    have hleft :
        ((⟨n - k - 1 + i.rev.val, by omega⟩ : Fin n).rev) =
          (⟨i.val, by omega⟩ : Fin n) := by
      apply Fin.ext
      simp
      omega
    have hright :
        ((⟨i.rev.val, by omega⟩ : Fin n).rev) =
          (⟨n - k - 1 + i.val, by omega⟩ : Fin n) := by
      apply Fin.ext
      simp
      omega
    change A ((⟨n - k - 1 + i.rev.val, by omega⟩ : Fin n).rev) =
      A ((⟨i.rev.val, by omega⟩ : Fin n).rev) at hi
    change A (⟨n - k - 1 + i.val, by omega⟩ : Fin n) =
      A (⟨i.val, by omega⟩ : Fin n)
    rw [hleft, hright] at hi
    exact hi.symm
  · intro h
    funext i
    have hi := congrFun h i.rev
    have hleft :
        ((⟨n - k - 1 + i.val, by omega⟩ : Fin n).rev) =
          (⟨i.rev.val, by omega⟩ : Fin n) := by
      apply Fin.ext
      simp
      omega
    have hright :
        ((⟨i.val, by omega⟩ : Fin n).rev) =
          (⟨n - k - 1 + i.rev.val, by omega⟩ : Fin n) := by
      apply Fin.ext
      simp
      omega
    change A ((⟨n - k - 1 + i.val, by omega⟩ : Fin n).rev) =
      A ((⟨i.val, by omega⟩ : Fin n).rev)
    change A (⟨n - k - 1 + i.rev.val, by omega⟩ : Fin n) =
      A (⟨i.rev.val, by omega⟩ : Fin n) at hi
    rw [hleft, hright]
    exact hi.symm

/-- Proper self-overlap numerators are invariant under reversal. -/
theorem overlapNum_reverse_self {n : ℕ} (A : Word n) :
    overlapNum (reverseWord A) (reverseWord A) = overlapNum A A := by
  unfold overlapNum
  apply Fintype.sum_congr
  intro k
  have hiff := reverse_self_overlap_iff A k
  by_cases hproper : k.val + 1 < n
  · by_cases hborder : wordSuffix A k = wordPrefix A k
    · have hrev := hiff.mpr hborder
      simp [hproper, hborder, hrev]
    · have hrev : wordSuffix (reverseWord A) k ≠
          wordPrefix (reverseWord A) k := fun h => hborder (hiff.mp h)
      simp [hproper, hborder, hrev]
  · simp [hproper]

/-- A word and its reversal have zero self-overlap difference. -/
theorem selfOverlapDelta_reverse {n : ℕ} (A : Word n) :
    selfOverlapDelta A (reverseWord A) = 0 := by
  simp [selfOverlapDelta, overlapNum_reverse_self]

#print axioms overlapNum_reverse_self
#print axioms selfOverlapDelta_reverse

end LittMostUnfairBet
