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

import FormalConjectures.OEIS.«308734Parity»

namespace OeisA308734

/-- The three possible restricted-coordinate patterns in the `7 mod 8` class. -/
def RestrictedSevenCases (n : ℕ) : Prop :=
  ∃ b d x y : ℕ,
    n = (3 ^ b) ^ 2 + (5 ^ d) ^ 2 + x ^ 2 + y ^ 2 ∨
    n = (2 * 3 ^ b) ^ 2 + (5 ^ d) ^ 2 + x ^ 2 + y ^ 2 ∨
    n = (3 ^ b) ^ 2 + (2 * 5 ^ d) ^ 2 + x ^ 2 + y ^ 2

private theorem not_both_even_residues_of_sum_four_squares_mod_eight_eq_seven :
    ∀ a b c d : Fin 8,
      (a.val ^ 2 + b.val ^ 2 + c.val ^ 2 + d.val ^ 2 ≡ 7 [MOD 8]) →
        ¬(Even a.val ∧ Even b.val) := by
  native_decide

private theorem even_mod_eight_of_even {n : ℕ} (h : Even n) : Even (n % 8) := by
  rw [even_iff_two_dvd] at h ⊢
  have hcong : n % 8 ≡ n [MOD 2] :=
    (Nat.mod_modEq n 8).of_dvd (by norm_num)
  exact Nat.modEq_zero_iff_dvd.mp (hcong.trans h.modEq_zero_nat)

/-- A sum of four squares that is seven modulo eight cannot have its first two bases even. -/
private theorem not_both_even_of_sum_four_squares_mod_eight_eq_seven {w x y z : ℕ}
    (h : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 ≡ 7 [MOD 8]) :
    ¬(Even w ∧ Even x) := by
  let W : Fin 8 := ⟨w % 8, Nat.mod_lt _ (by norm_num)⟩
  let X : Fin 8 := ⟨x % 8, Nat.mod_lt _ (by norm_num)⟩
  let Y : Fin 8 := ⟨y % 8, Nat.mod_lt _ (by norm_num)⟩
  let Z : Fin 8 := ⟨z % 8, Nat.mod_lt _ (by norm_num)⟩
  have hw : (w % 8) ^ 2 ≡ w ^ 2 [MOD 8] := (Nat.mod_modEq w 8).pow 2
  have hx : (x % 8) ^ 2 ≡ x ^ 2 [MOD 8] := (Nat.mod_modEq x 8).pow 2
  have hy : (y % 8) ^ 2 ≡ y ^ 2 [MOD 8] := (Nat.mod_modEq y 8).pow 2
  have hz : (z % 8) ^ 2 ≡ z ^ 2 [MOD 8] := (Nat.mod_modEq z 8).pow 2
  have hsum : W.val ^ 2 + X.val ^ 2 + Y.val ^ 2 + Z.val ^ 2 ≡ 7 [MOD 8] := by
    change (w % 8) ^ 2 + (x % 8) ^ 2 + (y % 8) ^ 2 + (z % 8) ^ 2 ≡ 7 [MOD 8]
    exact (((hw.add hx).add hy).add hz).trans h
  intro heven
  apply not_both_even_residues_of_sum_four_squares_mod_eight_eq_seven W X Y Z hsum
  exact ⟨even_mod_eight_of_even heven.1, even_mod_eight_of_even heven.2⟩

/-- In a representation of a number congruent to seven modulo eight, the restricted powers of two
are exactly one of `(0,0)`, `(1,0)`, or `(0,1)`. -/
theorem restricted_two_exponent_cases_of_mod_eight_eq_seven
    {n a b c d x y : ℕ} (hn : n % 8 = 7)
    (hrep : n = (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x ^ 2 + y ^ 2) :
    (a = 0 ∧ c = 0) ∨ (a = 1 ∧ c = 0) ∨ (a = 0 ∧ c = 1) := by
  obtain ⟨ha, hc⟩ := restricted_two_exponents_le_one_of_mod_eight_eq_seven hn hrep
  have hmod :
      (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x ^ 2 + y ^ 2 ≡ 7 [MOD 8] := by
    rw [← hrep]
    simpa [Nat.ModEq, hn]
  have hnot : ¬(a = 1 ∧ c = 1) := by
    rintro ⟨rfl, rfl⟩
    apply not_both_even_of_sum_four_squares_mod_eight_eq_seven hmod
    constructor <;> simp
  omega

/-- Exact reduction of the difficult `7 mod 8` class to three two-square families. -/
theorem isSumOfFourSquaresWithPowers_iff_restrictedSevenCases
    {n : ℕ} (hn : n % 8 = 7) :
    IsSumOfFourSquaresWithPowers n ↔ RestrictedSevenCases n := by
  constructor
  · rintro ⟨a, b, c, d, x, y, hrep⟩
    rcases restricted_two_exponent_cases_of_mod_eight_eq_seven hn hrep with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨b, d, x, y, Or.inl (by simpa using hrep)⟩
    · exact ⟨b, d, x, y, Or.inr (Or.inl (by simpa using hrep))⟩
    · exact ⟨b, d, x, y, Or.inr (Or.inr (by simpa using hrep))⟩
  · rintro ⟨b, d, x, y, h | h | h⟩
    · exact ⟨0, b, 0, d, x, y, by simpa using h⟩
    · exact ⟨1, b, 0, d, x, y, by simpa using h⟩
    · exact ⟨0, b, 1, d, x, y, by simpa using h⟩

end OeisA308734
