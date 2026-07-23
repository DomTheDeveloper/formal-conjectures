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

import FormalConjectures.Other.BeaverMathOlympiad8Correction

/-!
# Beaver Math Olympiad Problem 8 truncated-`Nat` certificate audit

This file preserves the previously green finite certificate, but states precisely what it proves:
the old two-branch recurrence over `ℕ`, whose subtraction truncates at zero.  It is not a solution
of the machine-faithful BMO #8 dynamics.

At zero-based index `1_210_682`, the truncated model reaches
`(1_749_056, 3_498_111)` and therefore satisfies the target equation.  The corrected dynamics
already diverge at the boundary state `(675, 1347)`.

Certificate and formal audit by Dominic Dabish with ProofOrchestrator.
-/

namespace BeaverMathOlympiad

private def bmo8_truncated_run : ℕ → BMO8State → BMO8State
  | 0, s => s
  | n + 1, s => bmo8_truncated_run n (bmo8TruncatedNatStep s)

private def bmo8_truncated_orbit (n : ℕ) : BMO8State :=
  bmo8_truncated_run n (10, 12)

/-- The tail-recursive evaluator commutes with one truncated-model step. -/
@[category API, AMS 5 11 68]
private lemma bmo8_truncated_run_step (n : ℕ) (s : BMO8State) :
    bmo8_truncated_run n (bmo8TruncatedNatStep s) =
      bmo8TruncatedNatStep (bmo8_truncated_run n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simpa only [bmo8_truncated_run] using ih (bmo8TruncatedNatStep s)

/-- The explicit truncated orbit satisfies one recurrence step. -/
@[category API, AMS 5 11 68]
private lemma bmo8_truncated_orbit_succ (n : ℕ) :
    bmo8_truncated_orbit (n + 1) = bmo8TruncatedNatStep (bmo8_truncated_orbit n) := by
  simpa only [bmo8_truncated_orbit, bmo8_truncated_run] using
    bmo8_truncated_run_step n (10, 12)

/--
The old green certificate is valid for the truncated-`Nat` recurrence exactly as encoded.
This theorem is intentionally labeled as a test result, not as a solved research conjecture.
-/
@[category test, AMS 5 11 68]
theorem beaver_math_olympiad_problem_8_truncated_nat_variant_positive :
    ∀ᵉ (a : ℕ → ℕ) (b : ℕ → ℕ)
    (a_ini : a 0 = 10)
    (a_rec : ∀ n, a (n + 1) =
      if b n / 2 < a n then a n - b n / 2 - 3 else 3 * a n + 5)
    (b_ini : b 0 = 12)
    (b_rec : ∀ n, b (n + 1) =
      if b n / 2 < a n then 3 * ((b n + 1) / 2) + 6 else b n - 2 * a n),
    ∃ i, a i = b i / 2 + 1 := by
  intro a b a_ini a_rec b_ini b_rec
  have h_eq : ∀ n, (a n, b n) = bmo8_truncated_orbit n := by
    intro n
    induction n with
    | zero =>
        simp [bmo8_truncated_orbit, bmo8_truncated_run, a_ini, b_ini]
    | succ n ih =>
        rw [bmo8_truncated_orbit_succ, ← ih]
        by_cases h : b n / 2 < a n <;>
          simp [bmo8TruncatedNatStep, h, a_rec, b_rec]
  refine ⟨1_210_682, ?_⟩
  have hcalc : bmo8_truncated_orbit 1_210_682 = (1_749_056, 3_498_111) := by
    native_decide
  have hstate := (h_eq 1_210_682).trans hcalc
  have ha : a 1_210_682 = 1_749_056 := by
    simpa using congrArg Prod.fst hstate
  have hb : b 1_210_682 = 3_498_111 := by
    simpa using congrArg Prod.snd hstate
  norm_num [ha, hb]

end BeaverMathOlympiad
