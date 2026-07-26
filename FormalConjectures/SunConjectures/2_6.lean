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

import Mathlib.NumberTheory.PrimeCounting
import FormalConjecturesUtil

/-!
# Zhi-Wei Sun's Conjecture 2.6

Let $\pi(x)$ denote the number of primes not exceeding $x$. For every integer
$n > 4$ and every $1 \leq k \leq n$, Sun conjectured

$$
\pi(kn)^{1/k} > \pi((k+1)n)^{1/(k+1)}.
$$

Because both prime-counting values are positive in this range, this is
equivalent to the integral power inequality

$$
\pi(kn)^{k+1} > \pi((k+1)n)^k,
$$

which is the form stated below.

*Reference:*
- Zhi-Wei Sun, ["Problems on combinatorial properties of primes"](https://arxiv.org/abs/1402.6641), Conjecture 2.6.
-/

namespace SunConjectures

open scoped Nat.Prime

/--
**Zhi-Wei Sun's Conjecture 2.6.** For $n > 4$ and $1 \leq k \leq n$,
$\pi(kn)^{k+1} > \pi((k+1)n)^k$.
-/
@[category research open, AMS 11]
theorem conjecture_2_6 (n k : ℕ) (hn : 4 < n) (hk_pos : 1 ≤ k) (hk_le : k ≤ n) :
    (π (k * n)) ^ (k + 1) > (π ((k + 1) * n)) ^ k := by
  sorry

end SunConjectures
