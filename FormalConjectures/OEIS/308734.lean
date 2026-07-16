/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Four-square conjecture with powers of 2, 3, and 5

Any integer $n > 1$ can be written as $(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$
where $a, b, c, d, x, y$ are nonnegative integers.

Zhi-Wei Sun has offered a $2,500 prize for the first proof.

*References:*
- [A308734](https://oeis.org/A308734)
- Z.-W. Sun, "Refining Lagrange's four-square theorem," *J. Number Theory* **175** (2017), 167-190.
  https://doi.org/10.1016/j.jnt.2016.11.008
- Z.-W. Sun, "Restricted sums of four squares," *Int. J. Number Theory* **15** (2019), 1863-1893.
- Z.-W. Sun, "Various Refinements of Lagrange's Four-Square Theorem," Westlake Number Theory
  Symposium, Nanjing University, China, 2020.
- S. Banerjee, "On a conjecture of Sun about sums of restricted squares," *J. Number Theory*
  **256** (2024), 253-289.
-/

namespace OeisA308734

/-- The predicate that `n` can be written as $(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$
for nonnegative integers $a, b, c, d, x, y$. -/
def IsSumOfFourSquaresWithPowers (n : ℕ) : Prop :=
  ∃ a b c d x y : ℕ, n = (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x ^ 2 + y ^ 2

@[category test, AMS 11]
theorem isSumOfFourSquaresWithPowers_2 : IsSumOfFourSquaresWithPowers 2 :=
  ⟨0, 0, 0, 0, 0, 0, by norm_num⟩

@[category test, AMS 11]
theorem isSumOfFourSquaresWithPowers_3 : IsSumOfFourSquaresWithPowers 3 :=
  ⟨0, 0, 0, 0, 0, 1, by norm_num⟩

@[category test, AMS 11]
theorem isSumOfFourSquaresWithPowers_4 : IsSumOfFourSquaresWithPowers 4 :=
  ⟨0, 0, 0, 0, 1, 1, by norm_num⟩

@[category test, AMS 11]
theorem isSumOfFourSquaresWithPowers_5 : IsSumOfFourSquaresWithPowers 5 :=
  ⟨1, 0, 0, 0, 0, 0, by norm_num⟩

/-- A representation scales by four: increment both powers of two and double the free squares. -/
theorem scale_four {n : ℕ} (hn : IsSumOfFourSquaresWithPowers n) :
    IsSumOfFourSquaresWithPowers (4 * n) := by
  rcases hn with ⟨a, b, c, d, x, y, h⟩
  refine ⟨a + 1, b, c + 1, d, 2 * x, 2 * y, ?_⟩
  rw [h]
  simp only [pow_succ]
  ring

private theorem even_residues_of_eight_dvd_sum_four_squares :
    ∀ a b c d : Fin 8,
      (a.val ^ 2 + b.val ^ 2 + c.val ^ 2 + d.val ^ 2 ≡ 0 [MOD 8]) →
        Even a.val ∧ Even b.val ∧ Even c.val ∧ Even d.val := by
  native_decide

private theorem even_of_even_mod_eight {n : ℕ} (h : Even (n % 8)) : Even n := by
  rw [even_iff_two_dvd] at h ⊢
  have hmod : n % 8 ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.mpr h
  have hcong : n % 8 ≡ n [MOD 2] :=
    (Nat.mod_modEq n 8).of_dvd (by norm_num)
  exact Nat.modEq_zero_iff_dvd.mp (hcong.symm.trans hmod)

/-- If four squares sum to a multiple of eight, then all four bases are even. -/
private theorem even_of_eight_dvd_sum_four_squares {w x y z : ℕ}
    (h : 8 ∣ w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) :
    Even w ∧ Even x ∧ Even y ∧ Even z := by
  let W : Fin 8 := ⟨w % 8, Nat.mod_lt _ (by norm_num)⟩
  let X : Fin 8 := ⟨x % 8, Nat.mod_lt _ (by norm_num)⟩
  let Y : Fin 8 := ⟨y % 8, Nat.mod_lt _ (by norm_num)⟩
  let Z : Fin 8 := ⟨z % 8, Nat.mod_lt _ (by norm_num)⟩
  have hw : w % 8 ^ 2 ≡ w ^ 2 [MOD 8] := (Nat.mod_modEq w 8).pow 2
  have hx : x % 8 ^ 2 ≡ x ^ 2 [MOD 8] := (Nat.mod_modEq x 8).pow 2
  have hy : y % 8 ^ 2 ≡ y ^ 2 [MOD 8] := (Nat.mod_modEq y 8).pow 2
  have hz : z % 8 ^ 2 ≡ z ^ 2 [MOD 8] := (Nat.mod_modEq z 8).pow 2
  have hsum : W.val ^ 2 + X.val ^ 2 + Y.val ^ 2 + Z.val ^ 2 ≡ 0 [MOD 8] := by
    change (w % 8) ^ 2 + (x % 8) ^ 2 + (y % 8) ^ 2 + (z % 8) ^ 2 ≡ 0 [MOD 8]
    exact (((hw.add hx).add hy).add hz).trans h.modEq_zero_nat
  obtain ⟨hw', hx', hy', hz'⟩ :=
    even_residues_of_eight_dvd_sum_four_squares W X Y Z hsum
  exact ⟨even_of_even_mod_eight hw', even_of_even_mod_eight hx',
    even_of_even_mod_eight hy', even_of_even_mod_eight hz'⟩

/-- For even `n`, a representation of `4 * n` descends to a representation of `n`. -/
theorem descale_four_of_even {n : ℕ} (hn : Even n)
    (hrep : IsSumOfFourSquaresWithPowers (4 * n)) : IsSumOfFourSquaresWithPowers n := by
  rcases hrep with ⟨a, b, c, d, x, y, h⟩
  have h8 : 8 ∣ (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x ^ 2 + y ^ 2 := by
    rw [← h]
    obtain ⟨k, hk⟩ := hn
    refine ⟨k, ?_⟩
    rw [hk]
    omega
  obtain ⟨hu, hv, hx, hy⟩ := even_of_eight_dvd_sum_four_squares h8
  cases a with
  | zero =>
      have hodd : Odd (3 ^ b) := (by norm_num : Odd (3 : ℕ)).pow
      exact (Nat.not_even_iff_odd.mpr hodd) (by simpa using hu)
  | succ a =>
      cases c with
      | zero =>
          have hodd : Odd (5 ^ d) := (by norm_num : Odd (5 : ℕ)).pow
          exact (Nat.not_even_iff_odd.mpr hodd) (by simpa using hv)
      | succ c =>
          rcases hx with ⟨x', hx'⟩
          rcases hy with ⟨y', hy'⟩
          refine ⟨a, b, c, d, x', y', ?_⟩
          have h4 :
              4 * n = 4 * ((2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x' ^ 2 + y' ^ 2) := by
            calc
              4 * n = (2 ^ (a + 1) * 3 ^ b) ^ 2 + (2 ^ (c + 1) * 5 ^ d) ^ 2 +
                  x ^ 2 + y ^ 2 := h
              _ = 4 * ((2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x' ^ 2 + y' ^ 2) := by
                rw [hx', hy']
                simp only [pow_succ]
                ring
          omega

/-- For even `n`, representability is invariant under multiplication by four. -/
theorem scale_four_iff_of_even {n : ℕ} (hn : Even n) :
    IsSumOfFourSquaresWithPowers (4 * n) ↔ IsSumOfFourSquaresWithPowers n :=
  ⟨descale_four_of_even hn, scale_four⟩

/-- It is enough to prove the conjecture for integers not divisible by four. -/
theorem conjecture_of_not_four_dvd
    (hprimitive : ∀ n : ℕ, 1 < n → ¬4 ∣ n → IsSumOfFourSquaresWithPowers n) :
    ∀ n : ℕ, 1 < n → IsSumOfFourSquaresWithPowers n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases h4 : 4 ∣ n
      · obtain ⟨m, rfl⟩ := h4
        by_cases hm : m = 1
        · subst m
          exact isSumOfFourSquaresWithPowers_4
        · have hmgt : 1 < m := by omega
          have hmlt : m < 4 * m := by omega
          exact scale_four (ih m hmlt hmgt)
      · exact hprimitive n hn h4

/--
**Zhi-Wei Sun's Four-Square Conjecture (A308734)**: Any integer $n > 1$ can be written as
$(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$ for nonnegative integers $a, b, c, d, x, y$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 1 < n) : IsSumOfFourSquaresWithPowers n := by
  sorry

end OeisA308734