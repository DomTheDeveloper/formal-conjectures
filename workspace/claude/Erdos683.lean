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

import FormalConjectures.ErdosProblems.«683»

/-!
# Resolution of the formal statement of Erdős Problem 683

`FormalConjectures/ErdosProblems/683.lean` states:

```
theorem erdos_683 : answer(sorry) ↔
    (∃ c > (0 : ℝ), ∀ n k : ℕ, 0 < k ∧ k < n → P n k > min (n - k + 1 : ℝ) (k ^ (1 + c)))
```

where `P n k` is the largest prime factor of `binom n k`.  The source problem
([erdosproblems.com/683](https://www.erdosproblems.com/683)) states the bound
*non-strictly*, `P(n,k) ≥ min(n-k+1, k^{1+c})`, precisely because equality
occurs for `k` close to `n`.  With the strict `>` the statement is false for
every `c > 0`, as `n = 4, k = 3` already shows:

* `binom 4 3 = 4`, so `P 4 3 = 2`;
* `n - k + 1 = 2` and `3 ^ (1 + c) > 3 > 2`, so the minimum is `2`;
* the required `2 > 2` is false.

(There are infinitely many such counterexamples: `n = 2 ^ t`, `k = n - 1`
gives `binom n k = n = 2 ^ t`, hence `P = 2 = n - k + 1`.)

So the formal statement is resolved by `answer(False)`, while the intended
`≥`-version remains open.
-/

namespace Erdos683Resolution

open Erdos683

/-- The largest prime factor of `binom 4 3 = 4` is `2`. -/
private lemma P_four_three : P 4 3 = 2 := by
  have hc : Nat.choose 4 3 = 2 ^ 2 := rfl
  have hpf : (2 ^ 2 : ℕ).primeFactors = {2} :=
    Nat.primeFactors_prime_pow (by norm_num) (by norm_num)
  show ((Nat.choose 4 3).primeFactors.sup id) = 2
  rw [hc, hpf]
  rfl

/-- The right-hand side of the formalized Erdős 683 is false: the strict
inequality fails at `n = 4`, `k = 3` for every `c > 0`. -/
theorem erdos_683_rhs_false :
    ¬ (∃ c > (0 : ℝ), ∀ n k : ℕ, 0 < k ∧ k < n →
        P n k > min (n - k + 1 : ℝ) (k ^ (1 + c))) := by
  rintro ⟨c, hc, h⟩
  have h43 := h 4 3 ⟨by norm_num, by norm_num⟩
  rw [P_four_three] at h43
  -- `3 ^ (1 + c) ≥ 3 > 2`, so the minimum is `(4 : ℝ) - 3 + 1 = 2`
  have hpow : (2 : ℝ) ≤ ((3 : ℕ) : ℝ) ^ (1 + c) := by
    have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rw [h3]
    calc (2 : ℝ) ≤ 3 := by norm_num
      _ = (3 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 3).symm
      _ ≤ (3 : ℝ) ^ (1 + c) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hle : ((4 : ℕ) : ℝ) - ((3 : ℕ) : ℝ) + 1 ≤ ((3 : ℕ) : ℝ) ^ (1 + c) := by
    have : ((4 : ℕ) : ℝ) - ((3 : ℕ) : ℝ) + 1 = 2 := by norm_num
    rw [this]
    exact hpow
  rw [min_eq_left hle] at h43
  norm_num at h43

end Erdos683Resolution
