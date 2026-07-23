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

import FormalConjectures.Other.LittMostUnfairBetWalshConstantGap
import FormalConjectures.Other.LittMostUnfairBetReversal

/-!
# Constant-interior two-endpoint Litt branch

The equal-endpoint case contains a constant word, so the already verified
constant-word Walsh bound gives the required energy gap. In the opposite-
endpoint case the second word is the reversal of the first, so their proper
self-overlap numerators agree.
-/

set_option autoImplicit false

namespace LittMostUnfairBetWalsh

open LittMostUnfairBet

/-- If the common interior is constant and the first word has equal endpoints,
then one of the two words is constant. Hence the full constant-word energy
bound applies. -/
theorem rawEnergy_ge_of_constant_interior_equal_endpoints {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n) (c : Bool)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hconst : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = c)
    (hleft : A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩)
    (hright : A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩)
    (hends : A ⟨0, by omega⟩ = A ⟨n - 1, by omega⟩) :
    16 * 2 ^ (n - 3) ≤ rawEnergy A B := by
  let left : Fin n := ⟨0, by omega⟩
  let right : Fin n := ⟨n - 1, by omega⟩
  have hleft' : A left ≠ B left := by simpa [left] using hleft
  have hright' : A right ≠ B right := by simpa [right] using hright
  have hends' : A left = A right := by simpa [left, right] using hends
  have hne : A ≠ B := by
    intro hAB
    exact hleft' (congrFun hAB left)
  have hconstant : IsConstant A ∨ IsConstant B := by
    by_cases hAc : A left = c
    · left
      refine ⟨c, ?_⟩
      funext i
      by_cases hi0 : i.val = 0
      · have hi : i = left := Fin.ext hi0
        subst i
        simpa [constantWord] using hAc
      by_cases hilast : i.val = n - 1
      · have hi : i = right := Fin.ext hilast
        subst i
        have hrightc : A right = c := by
          calc
            A right = A left := hends'.symm
            _ = c := hAc
        simpa [constantWord] using hrightc
      · have hi := hconst i (by omega) (by omega)
        simpa [constantWord] using hi
    · right
      have hAleft_ne : A left ≠ c := hAc
      have hAright_ne : A right ≠ c := by
        intro h
        apply hAleft_ne
        calc
          A left = A right := hends'
          _ = c := h
      have hBleft : B left = c := by
        cases hc : c <;>
          cases ha : A left <;>
          cases hb : B left <;>
          simp [hc, ha, hb] at hAleft_ne hleft' ⊢
      have hBright : B right = c := by
        cases hc : c <;>
          cases ha : A right <;>
          cases hb : B right <;>
          simp [hc, ha, hb] at hAright_ne hright' ⊢
      refine ⟨c, ?_⟩
      funext i
      by_cases hi0 : i.val = 0
      · have hi : i = left := Fin.ext hi0
        subst i
        simpa [constantWord] using hBleft
      by_cases hilast : i.val = n - 1
      · have hi : i = right := Fin.ext hilast
        subst i
        simpa [constantWord] using hBright
      · calc
          B i = A i := (hinterior i (by omega) (by omega)).symm
          _ = c := hconst i (by omega) (by omega)
          _ = constantWord n c i := by simp [constantWord]
  have hraw := rawEnergy_ge_of_constant A B hne hconstant
  have hpow : 16 * 2 ^ (n - 3) = 2 ^ (n + 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp [pow_add]
    ring
  rw [hpow]
  exact hraw

/-- If the common interior is constant and the first word has opposite
endpoints, differing at both endpoints makes the second word exactly the
reversal of the first. Reversal preserves every proper self-overlap. -/
theorem selfOverlapDelta_eq_zero_of_constant_interior_opposite_endpoints
    {n : ℕ} (hn : 3 ≤ n)
    (A B : Word n) (c : Bool)
    (hinterior : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = B i)
    (hconst : ∀ i : Fin n, 0 < i.val → i.val < n - 1 → A i = c)
    (hleft : A ⟨0, by omega⟩ ≠ B ⟨0, by omega⟩)
    (hright : A ⟨n - 1, by omega⟩ ≠ B ⟨n - 1, by omega⟩)
    (hends : A ⟨0, by omega⟩ ≠ A ⟨n - 1, by omega⟩) :
    selfOverlapDelta A B = 0 := by
  let left : Fin n := ⟨0, by omega⟩
  let right : Fin n := ⟨n - 1, by omega⟩
  have hleft' : A left ≠ B left := by simpa [left] using hleft
  have hright' : A right ≠ B right := by simpa [right] using hright
  have hends' : A left ≠ A right := by simpa [left, right] using hends
  have hBleft : B left = A right := by
    cases hal : A left <;>
      cases har : A right <;>
      cases hbl : B left <;>
      simp [hal, har, hbl] at hends' hleft' ⊢
  have hBright : B right = A left := by
    cases hal : A left <;>
      cases har : A right <;>
      cases hbr : B right <;>
      simp [hal, har, hbr] at hends' hright' ⊢
  have hrevLeft : left.rev = right := by
    apply Fin.ext
    dsimp [left, right, Fin.rev]
  have hrevRight : right.rev = left := by
    apply Fin.ext
    dsimp [left, right, Fin.rev]
    omega
  have hrev : B = reverseWord A := by
    funext i
    by_cases hi0 : i.val = 0
    · have hi : i = left := Fin.ext hi0
      subst i
      change B left = A left.rev
      rw [hrevLeft]
      exact hBleft
    by_cases hilast : i.val = n - 1
    · have hi : i = right := Fin.ext hilast
      subst i
      change B right = A right.rev
      rw [hrevRight]
      exact hBright
    · have hiPos : 0 < i.val := by omega
      have hiLast : i.val < n - 1 := by omega
      have hrevPos : 0 < i.rev.val := by
        simp only [Fin.rev, Fin.val_mk]
        omega
      have hrevLast : i.rev.val < n - 1 := by
        simp only [Fin.rev, Fin.val_mk]
        omega
      change B i = A i.rev
      calc
        B i = A i := (hinterior i hiPos hiLast).symm
        _ = c := hconst i hiPos hiLast
        _ = A i.rev := (hconst i.rev hrevPos hrevLast).symm
  rw [hrev]
  exact selfOverlapDelta_reverse A

#print axioms rawEnergy_ge_of_constant_interior_equal_endpoints
#print axioms selfOverlapDelta_eq_zero_of_constant_interior_opposite_endpoints

end LittMostUnfairBetWalsh
