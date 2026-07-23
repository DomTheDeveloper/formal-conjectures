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
# Maximum contacts on the honeycomb lattice

OEIS A263135 is the maximum number of contacts among `m` vertices of the
infinite honeycomb graph. The conjectured even-index closed form is

`A263135 (2 * n) = 3 * n - ceil (sqrt (3 * n))`.

*References:*
- [A263135](https://oeis.org/A263135)
- [A047932](https://oeis.org/A047932)
- [A216256](https://oeis.org/A216256)
- Berit Grußien, ["Isoperimetric Inequalities on Hexagonal Grids"](https://arxiv.org/abs/1201.0697)
-/

namespace OeisA263135

/-- The three edge directions incident to a vertex of the honeycomb graph. -/
inductive Direction
  | same
  | horizontal
  | diagonal
  deriving DecidableEq, Fintype

/-- A vertex `A i j` (`side = false`) or `B i j` (`side = true`). -/
structure Vertex where
  i : ℤ
  j : ℤ
  side : Bool
  deriving DecidableEq

/-- The neighbor of `v` in direction `d`. -/
def neighbor : Vertex → Direction → Vertex
  | ⟨i, j, false⟩, .same => ⟨i, j, true⟩
  | ⟨i, j, false⟩, .horizontal => ⟨i - 1, j, true⟩
  | ⟨i, j, false⟩, .diagonal => ⟨i, j - 1, true⟩
  | ⟨i, j, true⟩, .same => ⟨i, j, false⟩
  | ⟨i, j, true⟩, .horizontal => ⟨i + 1, j, false⟩
  | ⟨i, j, true⟩, .diagonal => ⟨i, j + 1, false⟩

/-- The number of honeycomb edges with both endpoints in `S`. -/
def contacts (S : Finset Vertex) : ℕ :=
  Finset.sum S fun v =>
    if v.side = true then 0
    else
      Finset.sum Finset.univ fun d : Direction =>
        if neighbor v d ∈ S then 1 else 0

/-- `k` is the maximum contact count among all `N`-vertex honeycomb subsets. -/
def IsMaximumContact (N k : ℕ) : Prop :=
  (∃ S : Finset Vertex, S.card = N ∧ contacts S = k) ∧
    ∀ S : Finset Vertex, S.card = N → contacts S ≤ k

/-- Exact natural-number characterization of `r = ceil (sqrt x)`. -/
def IsNatCeilSqrt (x r : ℕ) : Prop :=
  (r - 1) ^ 2 < x ∧ x ≤ r ^ 2

/--
**OEIS A263135, stronger even-index form.** For every positive `n`, the maximum
number of contacts among `2 * n` vertices of the infinite honeycomb graph is
`3 * n - ceil (sqrt (3 * n))`.
-/
@[category research open, AMS 05]
theorem conjecture (n : ℕ) (hn : 0 < n) :
    ∃ r : ℕ, IsNatCeilSqrt (3 * n) r ∧
      IsMaximumContact (2 * n) (3 * n - r) := by
  sorry

end OeisA263135
