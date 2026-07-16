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

import FormalConjectures.OEIS.«308734»

namespace OeisA308734

private theorem no_four_dvd_residues_of_sum_four_squares_mod_eight_eq_seven :
    ∀ a b c d : Fin 8,
      (a.val ^ 2 + b.val ^ 2 + c.val ^ 2 + d.val ^ 2 ≡ 7 [MOD 8]) →
        ¬ 4 ∣ a.val ∧ ¬ 4 ∣ b.val ∧ ¬ 4 ∣ c.val ∧ ¬ 4 ∣ d.val := by
  native_decide

private theorem no_four_dvd_of_no_four_dvd_mod_eight {n : ℕ}
    (h : ¬ 4 ∣ n % 8) : ¬ 4 ∣ n := by
  intro hn
  apply h
  have hcong : n % 8 ≡ n [MOD 4] :=
    (Nat.mod_modEq n 8).of_dvd (by norm_num)
  exact Nat.modEq_zero_iff_dvd.mp (hcong.trans hn.modEq_zero_nat)

/-- If four squares sum to seven modulo eight, none of their bases is divisible by four. -/
theorem no_four_dvd_of_sum_four_squares_mod_eight_eq_seven {w x y z : ℕ}
    (h : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 ≡ 7 [MOD 8]) :
    ¬ 4 ∣ w ∧ ¬ 4 ∣ x ∧ ¬ 4 ∣ y ∧ ¬ 4 ∣ z := by
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
  obtain ⟨hw', hx', hy', hz'⟩ :=
    no_four_dvd_residues_of_sum_four_squares_mod_eight_eq_seven W X Y Z hsum
  exact ⟨no_four_dvd_of_no_four_dvd_mod_eight (by simpa [W] using hw'),
    no_four_dvd_of_no_four_dvd_mod_eight (by simpa [X] using hx'),
    no_four_dvd_of_no_four_dvd_mod_eight (by simpa [Y] using hy'),
    no_four_dvd_of_no_four_dvd_mod_eight (by simpa [Z] using hz')⟩

/-- In the difficult `7 mod 8` class, both restricted powers of two are at most one. -/
theorem restricted_two_exponents_le_one_of_mod_eight_eq_seven
    {n a b c d x y : ℕ} (hn : n % 8 = 7)
    (hrep : n = (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x ^ 2 + y ^ 2) :
    a ≤ 1 ∧ c ≤ 1 := by
  have hmod :
      (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x ^ 2 + y ^ 2 ≡ 7 [MOD 8] := by
    rw [← hrep]
    simpa [Nat.ModEq, hn]
  obtain ⟨hu, hv, _, _⟩ := no_four_dvd_of_sum_four_squares_mod_eight_eq_seven hmod
  constructor
  · cases a with
    | zero => omega
    | succ a =>
        cases a with
        | zero => omega
        | succ a =>
            exfalso
            apply hu
            refine ⟨2 ^ a * 3 ^ b, ?_⟩
            simp only [pow_succ]
            ring
  · cases c with
    | zero => omega
    | succ c =>
        cases c with
        | zero => omega
        | succ c =>
            exfalso
            apply hv
            refine ⟨2 ^ c * 5 ^ d, ?_⟩
            simp only [pow_succ]
            ring

end OeisA308734
