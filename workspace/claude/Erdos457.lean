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

import FormalConjectures.ErdosProblems.«457»

/-!
# `erdos_457.variants.qnk` follows from the solved `erdos_457`

`FormalConjectures/ErdosProblems/457.lean` contains:

* `erdos_457`, tagged **`research solved`** with `answer(True)` and a linked
  external Lean proof (Barreto–van Doorn, using Aristotle):
  `∃ ε > 0, {n | ∀ p ≤ (2+ε) log n, p.Prime → p ∣ ∏_{1≤i≤log n} (n+i)}.Infinite`;
* `erdos_457.variants.qnk`, tagged **`research open`**:
  `∃ ε > 0, {n | (2+ε) log n ≤ q n (log n)}.Infinite`, where `q n k` is the
  least prime *not* dividing `∏_{1≤i≤k} (n+i)`.

These are the same statement read two ways.  If every prime `p ≤ (2+ε) log n`
divides the product, then the least prime that does *not* divide it must
exceed `(2+ε) log n`.  So the `erdos_457` set is contained in the `qnk` set
*for the very same `ε`*, and infinitude transfers directly.

This file proves that implication, sorry-free, so the answer to
`erdos_457.variants.qnk` is `True` and it is not an additional open problem.
Since `erdos_457` is itself `sorry`-ed in the repository, the result is stated
as an implication from its right-hand side — which is exactly the point: no
new mathematics separates the two.
-/

open Filter

namespace Erdos457Resolution

/-- If every prime up to `(2 + ε) log n` divides `∏_{1 ≤ i ≤ log n} (n + i)`,
then the least prime *not* dividing that product is at least `(2 + ε) log n`. -/
theorem le_q_of_forall_prime_dvd {ε : ℝ} {n : ℕ}
    (h : ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
      p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i)) :
    (2 + ε) * Real.log n ≤ Erdos457.q n (Real.log n) := by
  by_contra hlt
  push_neg at hlt
  -- `q` is prime and does not divide the product, by `Nat.find_spec`
  have hspec := Nat.find_spec (Nat.exists_prime_not_dvd
    (∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i))
    (Finset.prod_ne_zero_iff.2 fun a ha => by aesop))
  -- but then it is a prime below the bound, so it must divide it
  exact hspec.2 (h _ hlt.le hspec.1)

/-- **The right-hand side of `erdos_457.variants.qnk` follows from the
right-hand side of the solved `erdos_457`** (with the same `ε`). -/
theorem qnk_of_erdos_457
    (h : ∃ ε > (0 : ℝ),
      { (n : ℕ) | ∀ (p : ℕ), p ≤ (2 + ε) * Real.log n → p.Prime →
        p ∣ ∏ i ∈ Finset.Icc 1 ⌊Real.log n⌋₊, (n + i) }.Infinite) :
    ∃ ε > (0 : ℝ),
      { (n : ℕ) | (2 + ε) * Real.log n ≤ Erdos457.q n (Real.log n) }.Infinite := by
  obtain ⟨ε, hε, hinf⟩ := h
  refine ⟨ε, hε, hinf.mono ?_⟩
  intro n hn
  exact le_q_of_forall_prime_dvd hn

end Erdos457Resolution
