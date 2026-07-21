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

import FormalConjecturesUtil

/-!
# Beaver Math Olympiad Problem 4

A dedicated fork-hosted Lean proof of the theorem stated in
`FormalConjectures/Other/BeaverMathOlympiad.lean`.
-/

namespace BeaverMathOlympiad

/-- Exact Lean proof of Beaver Math Olympiad Problem 4. -/
theorem beaver_math_olympiad_problem_4_proof
    (a : ℕ → ℕ)
    (a_ini : a 0 = 2)
    (a_rec : ∀ n, a (n+1)
      = if a n % 3 = 0 then a n / 3 + 2 ^ n + 1 else (a n - 2) / 3 + 2 ^ n - 1) :
    ¬ (∃ n, a n % 3 = 1) := by
  have hclosed : ∀ n : ℕ,
      (n % 4 = 0 ∧ 5 * a n = 3 * 2 ^ n + 7) ∨
      (n % 4 = 1 ∧ 5 * a n + 6 = 3 * 2 ^ n) ∨
      (n % 4 = 2 ∧ 5 * a n = 3 * 2 ^ n + 3) ∨
      (n % 4 = 3 ∧ 5 * a n = 3 * 2 ^ n + 6) := by
    intro n
    induction n with
    | zero =>
        exact Or.inl ⟨by norm_num, by norm_num [a_ini]⟩
    | succ n ih =>
        rcases ih with h0 | h1 | h2 | h3
        · rcases h0 with ⟨hn4, hform⟩
          have hamod : a n % 3 = 2 := by omega
          have hdiv : a n = 3 * ((a n - 2) / 3) + 2 := by omega
          refine Or.inr (Or.inl ⟨?_, ?_⟩)
          · omega
          · rw [a_rec n]
            simp [hamod, pow_succ]
            omega
        · rcases h1 with ⟨hn4, hform⟩
          have hamod : a n % 3 = 0 := by omega
          have hdiv : a n = 3 * (a n / 3) := by omega
          refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
          · omega
          · rw [a_rec n]
            simp [hamod, pow_succ]
            omega
        · rcases h2 with ⟨hn4, hform⟩
          have hamod : a n % 3 = 0 := by omega
          have hdiv : a n = 3 * (a n / 3) := by omega
          refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
          · omega
          · rw [a_rec n]
            simp [hamod, pow_succ]
            omega
        · rcases h3 with ⟨hn4, hform⟩
          have hamod : a n % 3 = 0 := by omega
          have hdiv : a n = 3 * (a n / 3) := by omega
          refine Or.inl ⟨?_, ?_⟩
          · omega
          · rw [a_rec n]
            simp [hamod, pow_succ]
            omega
  rintro ⟨n, hn⟩
  rcases hclosed n with h0 | h1 | h2 | h3
  · omega
  · omega
  · omega
  · omega

#print axioms beaver_math_olympiad_problem_4_proof

end BeaverMathOlympiad
