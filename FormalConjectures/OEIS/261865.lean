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
module

public import FormalConjecturesUtil
public import FormalConjecturesForMathlib.Analysis.Equidistribution.UnitAddTorus

@[expose] public section

/-!
# OEIS A261865 / Peter Kagey's Problem 13

For a positive integer `n`, OEIS A261865 is the least positive integer `k`
for which a positive integer multiple of `√k` lies strictly between `n` and
`n + 1`.

Peter Kagey's Problem 13 asks for the natural density of the indices at which
a fixed squarefree `j ≥ 2` is the least successful radicand.  The predicted
density is

`(1 / √j) * ∏_{2 ≤ s < j, Squarefree s} (1 - 1 / √s)`.
-/

open Filter
open scoped BigOperators Topology

namespace OeisA261865

/-- A positive integer multiple of `√k` lies strictly in `(n, n + 1)`. -/
def Hits (k n : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧
    (n : ℝ) < (m : ℝ) * Real.sqrt (k : ℝ) ∧
      (m : ℝ) * Real.sqrt (k : ℝ) < (n : ℝ) + 1

/-- `k` is the least positive radicand that hits the interval `(n, n + 1)`. -/
def IsValue (n k : ℕ) : Prop :=
  0 < k ∧ Hits k n ∧ ∀ r : ℕ, 0 < r → r < k → ¬ Hits r n

/-- The squarefree integers in `[2, j)`. -/
noncomputable def squarefreeBelow (j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico 2 j).filter Squarefree

/-- The density predicted for the value `j` in OEIS A261865. -/
noncomputable def predictedDensity (j : ℕ) : ℝ :=
  (1 / Real.sqrt (j : ℝ)) *
    ∏ s ∈ squarefreeBelow j, (1 - 1 / Real.sqrt (s : ℝ))

/--
**Peter Kagey's Problem 13 / OEIS A261865.**

For every squarefree `j ≥ 2`, the set of positive indices where the least
successful radicand is `j` has the stated natural density.
-/
@[category research open, AMS 11]
theorem density_formula (j : ℕ) (hj : 2 ≤ j) (hsq : Squarefree j) :
    {n : ℕ | 0 < n ∧ IsValue n j}.HasDensity (predictedDensity j) := by
  sorry

end OeisA261865
