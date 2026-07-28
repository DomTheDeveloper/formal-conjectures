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

import FormalConjectures.GreensOpenProblems.«1»

/-!
# Green's Problem 1 has been solved: `answer(True)`

`FormalConjectures/GreensOpenProblems/1.lean` states, tagged `research open`:

```
theorem green_1 : answer(sorry) ↔ ∃ Ω : ℕ → ℝ, atTop.Tendsto Ω atTop ∧
     ∀ n, ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) → A.card = n →
     ∃ (S : Finset ℕ), S ⊆ A ∧ IsSumFree (S : Set ℕ) ∧ ((n : ℝ) / 3) + Ω n ≤ S.card
```

This is Erdős's 1965 question, and it was **resolved affirmatively** by
Benjamin Bedert, *Large sum-free subsets of sets of integers via `L¹`-estimates
for trigonometric series* ([arXiv:2502.08624](https://arxiv.org/abs/2502.08624)):
there is `c > 0` such that every set of `n` integers contains a sum-free
subset of size at least `n/3 + c · log log n`.  Ben Green's own 2025 update to
the 100-problems list records Problem 1 as solved; see also
[Quanta](https://www.quantamagazine.org/graduate-student-solves-classic-problem-about-the-limits-of-addition-20250522/).

Bedert's bound is asymptotic (valid for large `n`), whereas the repository
statement quantifies over **all** `n`.  This file closes that gap: it proves,
sorry-free, that the asymptotic form implies the repository's form, so the
answer to `green_1` is `True`.

Formalizing Bedert's 36-page argument itself is well beyond this file; what is
proved here is the (routine, but not vacuous) reduction, together with the
observation that the small-`n` cases are absorbed by letting `Ω` be very
negative there — which is legitimate precisely because `Ω` is only required to
tend to infinity.
-/

open Filter

namespace Green1Resolution

/-- The empty set is sum-free. -/
lemma isSumFree_empty : IsSumFree (∅ : Set ℕ) := by
  simp [IsSumFree]

/-- `n ↦ c * log (log n)` tends to infinity for `c > 0`. -/
lemma tendsto_loglog {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => c * Real.log (Real.log n)) atTop atTop := by
  apply Filter.Tendsto.const_mul_atTop hc
  exact Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- **Bedert's theorem implies the repository's statement of Green's Problem 1.**

The hypothesis is Bedert's result: for some `c > 0` and all sufficiently large
`n`, every `n`-element set of positive integers has a sum-free subset of size
at least `n/3 + c log log n`. -/
theorem green_1_of_bedert
    (h : ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (A : Finset ℕ),
      (∀ a ∈ A, 0 < a) → A.card = n →
      ∃ (S : Finset ℕ), S ⊆ A ∧ IsSumFree (S : Set ℕ) ∧
        ((n : ℝ) / 3) + c * Real.log (Real.log n) ≤ S.card) :
    ∃ Ω : ℕ → ℝ, atTop.Tendsto Ω atTop ∧
      ∀ n, ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) → A.card = n →
      ∃ (S : Finset ℕ), S ⊆ A ∧ IsSumFree (S : Set ℕ) ∧ ((n : ℝ) / 3) + Ω n ≤ S.card := by
  obtain ⟨c, hc, n₀, hbed⟩ := h
  -- below `n₀` we make `Ω` very negative, which costs nothing since `Ω` need
  -- only tend to infinity
  refine ⟨fun n => if n₀ ≤ n then c * Real.log (Real.log n) else -(n : ℝ), ?_, ?_⟩
  · -- eventually the function agrees with `c log log n`
    apply Filter.Tendsto.congr' _ (tendsto_loglog hc)
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
    simp [hn]
  · intro n A hApos hAcard
    by_cases hn : n₀ ≤ n
    · simpa [hn] using hbed n hn A hApos hAcard
    · -- take `S = ∅`: we need `n/3 - n ≤ 0`
      refine ⟨∅, Finset.empty_subset _, by simpa using isSumFree_empty, ?_⟩
      simp only [hn, if_false, Finset.card_empty, Nat.cast_zero]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith

end Green1Resolution
