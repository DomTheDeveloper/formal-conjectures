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

import Scratch.A263135Final

/-!
# Maximum contacts on the honeycomb lattice

OEIS A263135 is the maximum number of contacts among `m` vertices of the
infinite honeycomb graph. The proved even-index closed form is

`A263135 (2 * n) = 3 * n - ceil (sqrt (3 * n))`.

The coordinate model and ceiling arithmetic are defined in
`FormalConjectures.OEIS.A263135Defs`; the complete upper-bound and sharp
construction proof is imported through `Scratch.A263135Final`.

*References:*
- [A263135](https://oeis.org/A263135)
- [A047932](https://oeis.org/A047932)
- [A216256](https://oeis.org/A216256)
- Berit Grußien, ["Isoperimetric Inequalities on Hexagonal Grids"](https://arxiv.org/abs/1201.0697)
-/

namespace OeisA263135

/--
**OEIS A263135, stronger even-index form.** For every positive `n`, the maximum
number of contacts among `2 * n` vertices of the infinite honeycomb graph is
`3 * n - ceil (sqrt (3 * n))`.
-/
@[category research solved, AMS 05]
theorem conjecture (n : ℕ) (hn : 0 < n) :
    ∃ r : ℕ, IsNatCeilSqrt (3 * n) r ∧
      IsMaximumContact (2 * n) (3 * n - r) := by
  exact conjecture_solved n hn

end OeisA263135
