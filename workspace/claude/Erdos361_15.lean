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

import FormalConjectures.Util.ProblemImports

/-!
# Resolutions of the formal statements of Erdős Problems 361 and 15

## Erdős 361 (`FormalConjectures/ErdosProblems/361.lean`)

All three statements `erdos_361.bigO` / `bigTheta` / `smallO` carry the
hypothesis

```
hA : ∀ c n, A n = ((Finset.Icc 1 ⌊c * n⌋₊).powerset.filter
       (fun B ↦ n ≠ ∑ a ∈ B, a)).sup Finset.card
```

where the binder `c` *shadows* the fixed parameter `c : ℝ` of the theorem (the
inner `c` even elaborates at type ℕ, so the outer `c` is entirely unused).
The hypothesis pins `A n` to a value for EVERY `c` simultaneously and is
contradictory: with `c = 1, n = 1` it forces `A 1 = 0`, while with
`c = 3, n = 1` it forces `A 1 = 3`.  Hence all three "open" statements are
vacuously provable, with any answer whatsoever.  The intended hypothesis uses
the theorem's real parameter `c` (i.e. `hA : ∀ n, A n = ...`).

## Erdős 15 (`FormalConjectures/ErdosProblems/15.lean`)

The problem asks whether `∑ (-1)^n n / p_n` *converges* (conditionally — a
genuinely open question about prime gaps).  The formal statement instead asks
for `Summable`, which in mathlib means unconditional summability; over ℚ (or
after casting, over ℝ) this forces absolute summability.  Since
`|(-1)^(k+1) (k+1) / p_k| ≥ 1/p_k` and `∑ 1/p` over the primes diverges
(mathlib's `not_summable_one_div_on_primes`), the right-hand side is FALSE, so
the formal statement is resolved by `answer(False)` — without touching the
open convergence question.
-/

open Filter Finset

namespace Erdos361Resolution

/-- The hypothesis shared by all three Erdős 361 statements is contradictory:
instantiating its universally quantified `c` at `1` and at `3` gives
`A 1 = 0` and `A 1 = 3`. -/
theorem erdos_361_hypothesis_inconsistent
    (A : ℕ → ℕ)
    (hA : ∀ (c n : ℕ), A n = ((Finset.Icc 1 ⌊c * n⌋₊).powerset.filter
      (fun B ↦ n ≠ ∑ a ∈ B, a)).sup Finset.card) :
    False :=
  absurd ((hA 1 1).symm.trans (hA 3 1)) (by decide)

/-- `erdos_361.bigO` as stated, with (for instance) the zero function as the
answer: vacuously true because the hypothesis is contradictory. -/
theorem erdos_361_bigO_vacuous
    (c : ℝ) (_hc : 0 < c)
    (A : ℕ → ℕ)
    (hA : ∀ c n, A n = ((Finset.Icc 1 ⌊c * n⌋₊).powerset.filter
      (fun B ↦ n ≠ ∑ a ∈ B, a)).sup Finset.card) :
    (fun n ↦ (A n : ℝ)) =O[atTop] ((fun _ => 0) : ℕ → ℝ) :=
  absurd hA (fun h => erdos_361_hypothesis_inconsistent A h)

/-- `erdos_361.bigTheta` as stated: vacuously true. -/
theorem erdos_361_bigTheta_vacuous
    (c : ℝ) (_hc : 0 < c)
    (A : ℕ → ℕ)
    (hA : ∀ c n, A n = ((Finset.Icc 1 ⌊c * n⌋₊).powerset.filter
      (fun B ↦ n ≠ ∑ a ∈ B, a)).sup Finset.card) :
    (fun n ↦ (A n : ℝ)) =Θ[atTop] ((fun _ => 0) : ℕ → ℝ) :=
  absurd hA (fun h => erdos_361_hypothesis_inconsistent A h)

/-- `erdos_361.smallO` as stated: vacuously true. -/
theorem erdos_361_smallO_vacuous
    (c : ℝ) (_hc : 0 < c)
    (A : ℕ → ℕ)
    (hA : ∀ c n, A n = ((Finset.Icc 1 ⌊c * n⌋₊).powerset.filter
      (fun B ↦ n ≠ ∑ a ∈ B, a)).sup Finset.card) :
    (fun n ↦ (A n : ℝ)) =o[atTop] ((fun _ => 0) : ℕ → ℝ) :=
  absurd hA (fun h => erdos_361_hypothesis_inconsistent A h)

end Erdos361Resolution

namespace Erdos15Resolution

/-- The right-hand side of the formalized Erdős 15 is false: mathlib's
`Summable` demands unconditional (hence absolute) convergence, and the terms
dominate `1/p_k`, whose sum over primes diverges.  So `erdos_15` is resolved
by `answer(False)`; the intended (conditional-convergence) question remains
open. -/
theorem erdos_15_rhs_false :
    ¬ Summable (fun k : ℕ => (-1 : ℚ) ^ (k + 1) * (k + 1) / (k.nth Nat.Prime)) := by
  intro hsum
  -- Cast the summability to ℝ.
  have hR : Summable (fun k : ℕ =>
      (((-1 : ℚ) ^ (k + 1) * (k + 1) / (k.nth Nat.Prime) : ℚ) : ℝ)) :=
    hsum.map (Rat.castHom ℝ).toAddMonoidHom Rat.continuous_coe_real
  have hR' : Summable (fun k : ℕ => ((-1 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) / (k.nth Nat.Prime))) := by
    convert hR using 2 with k
    push_cast
    ring
  -- Hence the absolute values are summable.
  have habs : Summable (fun k : ℕ => |(-1 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) / (k.nth Nat.Prime)|) :=
    summable_abs_iff.mpr hR'
  -- The absolute values dominate the indicator of the primes evaluated along `nth Prime`.
  set g : ℕ → ℝ := {p | p.Prime}.indicator (fun n => 1 / (n : ℝ)) with hg
  have hnth_prime : ∀ k, (Nat.nth Nat.Prime k).Prime := fun k =>
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
  have hcomp : Summable (fun k => g (Nat.nth Nat.Prime k)) := by
    apply Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) habs
    · exact Set.indicator_nonneg (fun n _ => by positivity) _
    · have hp := hnth_prime k
      have hppos : (0 : ℝ) < (Nat.nth Nat.Prime k : ℝ) := by exact_mod_cast hp.pos
      rw [hg, Set.indicator_of_mem (by exact hp : Nat.nth Nat.Prime k ∈ {p | p.Prime})]
      have habs_eq : |(-1 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) / (Nat.nth Nat.Prime k)|
          = ((k : ℝ) + 1) / (Nat.nth Nat.Prime k) := by
        rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1), abs_of_nonneg hppos.le]
      rw [habs_eq, div_le_div_iff_of_pos_right hppos]
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
  -- Transfer along the injection `nth Prime` to the full indicator sum.
  have hfull : Summable g := by
    rw [← Function.Injective.summable_iff
      (Nat.nth_injective Nat.infinite_setOf_prime) (fun x hx => ?_)]
    · exact hcomp
    · rw [hg, Set.indicator_of_notMem]
      rwa [Nat.range_nth_of_infinite Nat.infinite_setOf_prime] at hx
  exact not_summable_one_div_on_primes hfull

end Erdos15Resolution
