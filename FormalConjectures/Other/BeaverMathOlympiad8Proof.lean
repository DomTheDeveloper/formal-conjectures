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

import FormalConjectures.Other.BeaverMathOlympiad

/-!
# Beaver Math Olympiad Problem 8 Certificate

A finite Lean certificate for the positive answer to BMO #8. The recurrence reaches
`(1_749_056, 3_498_111)` at zero-based index `1_210_682`.
-/

namespace BeaverMathOlympiad

private def bmo8_step : ℕ × ℕ → ℕ × ℕ
  | (a, b) =>
      if b / 2 < a then
        (a - b / 2 - 3, 3 * ((b + 1) / 2) + 6)
      else
        (3 * a + 5, b - 2 * a)

private def bmo8_run : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, s => s
  | n + 1, s => bmo8_run n (bmo8_step s)

private def bmo8_orbit (n : ℕ) : ℕ × ℕ :=
  bmo8_run n (10, 12)

private lemma bmo8_run_step (n : ℕ) (s : ℕ × ℕ) :
    bmo8_run n (bmo8_step s) = bmo8_step (bmo8_run n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simpa only [bmo8_run] using ih (bmo8_step s)

private lemma bmo8_orbit_succ (n : ℕ) :
    bmo8_orbit (n + 1) = bmo8_step (bmo8_orbit n) := by
  simpa only [bmo8_orbit, bmo8_run] using bmo8_run_step n (10, 12)

/-- The BMO #8 recurrence has a target-hitting term. -/
@[category test, AMS 5 11 68]
theorem beaver_math_olympiad_problem_8_positive :
    ∀ᵉ (a : ℕ → ℕ) (b : ℕ → ℕ)
    (a_ini : a 0 = 10)
    (a_rec : ∀ n, a (n + 1) =
      if b n / 2 < a n then a n - b n / 2 - 3 else 3 * a n + 5)
    (b_ini : b 0 = 12)
    (b_rec : ∀ n, b (n + 1) =
      if b n / 2 < a n then 3 * ((b n + 1) / 2) + 6 else b n - 2 * a n),
    ∃ i, a i = b i / 2 + 1 := by
  intro a b a_ini a_rec b_ini b_rec
  have h_eq : ∀ n, (a n, b n) = bmo8_orbit n := by
    intro n
    induction n with
    | zero =>
        simp [bmo8_orbit, bmo8_run, a_ini, b_ini]
    | succ n ih =>
        rw [bmo8_orbit_succ, ← ih]
        by_cases h : b n / 2 < a n <;>
          simp [bmo8_step, h, a_rec, b_rec]
  refine ⟨1_210_682, ?_⟩
  have hcalc : bmo8_orbit 1_210_682 = (1_749_056, 3_498_111) := by
    native_decide
  have hstate := (h_eq 1_210_682).trans hcalc
  have ha : a 1_210_682 = 1_749_056 := by
    simpa using congrArg Prod.fst hstate
  have hb : b 1_210_682 = 3_498_111 := by
    simpa using congrArg Prod.snd hstate
  norm_num [ha, hb]

/-- BMO #8 has the positive answer. -/
@[category research solved, AMS 5 11 68]
theorem beaver_math_olympiad_problem_8_solved : answer(True) ↔
    ∀ᵉ (a : ℕ → ℕ) (b : ℕ → ℕ)
    (a_ini : a 0 = 10)
    (a_rec : ∀ n, a (n + 1) =
      if b n / 2 < a n then a n - b n / 2 - 3 else 3 * a n + 5)
    (b_ini : b 0 = 12)
    (b_rec : ∀ n, b (n + 1) =
      if b n / 2 < a n then 3 * ((b n + 1) / 2) + 6 else b n - 2 * a n),
    ∃ i, a i = b i / 2 + 1 := by
  constructor
  · intro _
    exact beaver_math_olympiad_problem_8_positive
  · intro _
    trivial

end BeaverMathOlympiad
