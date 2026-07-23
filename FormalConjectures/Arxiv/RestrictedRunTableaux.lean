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
import FormalConjecturesForMathlib.Combinatorics.RestrictedRunTableaux

/-!
# Standard Young tableaux with restricted runs

Kauers and Zeilberger's Conjecture 2a predicts the asymptotic number of
standard Young tableaux of rectangular shape `(n, n, n)` in which every
maximal string of consecutive entries lying in one row has length at least two.

The standard ballot-word encoding records the row containing each successive
entry. Consequently, `RestrictedRunTableaux.G n` counts three-letter ballot
words with content `(n, n, n)` and no singleton constant run. Its first values
for positive `n` are `0, 1, 1, 5, 15, 69, 304, 1518, 7807, 42314`.

*Reference:*

- [M. Kauers and D. Zeilberger, *Counting Standard Young Tableaux With
  Restricted Runs*](https://arxiv.org/abs/2006.10205)
-/

open Filter
open scoped Topology

namespace RestrictedRunTableaux

/--
**Kauers–Zeilberger Conjecture 2a.**

There is a positive constant `C₁` such that

`G(n) ∼ C₁ · 8ⁿ / n⁴`.

The limit formulation avoids division by `n⁴` at `n = 0` while expressing the
same asymptotic assertion.
-/
@[category research open, AMS 05]
theorem conjecture_2a :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      Tendsto
        (fun n : ℕ => ((G n : ℝ) * (n : ℝ) ^ 4) / (8 : ℝ) ^ n)
        atTop (𝓝 C₁) := by
  sorry

end RestrictedRunTableaux
