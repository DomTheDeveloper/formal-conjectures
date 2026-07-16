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
