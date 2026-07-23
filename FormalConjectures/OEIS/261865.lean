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
# OEIS A261865 / Peter Kagey's Problem 13

For a positive integer `n`, A261865 is the least positive integer `k` for
which a positive integer multiple of `√k` lies strictly between `n` and
`n + 1`.

For every squarefree `j ≥ 2`, the set of positive indices where the sequence
has value `j` has natural density

`(1 / √j) * ∏_{2 ≤ s < j, Squarefree s} (1 - 1 / √s)`.

The proof converts the interval-hitting conditions into terminal arcs for a
finite torus rotation. Rational independence of the reciprocal square roots
and multidimensional Weyl equidistribution then reduce the density to the Haar
measure of the corresponding terminal box.

*References:*
- [OEIS A261865](https://oeis.org/A261865)
-/

open Filter
open scoped BigOperators

namespace OeisA261865

/-- A positive integer multiple of `√k` lies strictly in `(n, n + 1)`. -/
def Hits (k n : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧
    (n : ℝ) < (m : ℝ) * Real.sqrt (k : ℝ) ∧
      (m : ℝ) * Real.sqrt (k : ℝ) < (n : ℝ) + 1

/-- `k` is the least positive radicand that hits `(n, n + 1)`. -/
def IsValue (n k : ℕ) : Prop :=
  0 < k ∧ Hits k n ∧ ∀ r : ℕ, 0 < r → r < k → ¬ Hits r n

/-- The density predicted for the value `j` in OEIS A261865. -/
noncomputable def predictedDensity (j : ℕ) : ℝ :=
  (1 / Real.sqrt (j : ℝ)) *
    ∏ s ∈ (Finset.Ico 2 j).filter Squarefree,
      (1 - 1 / Real.sqrt (s : ℝ))

/--
For every squarefree `j ≥ 2`, the positive indices where `j` is the least
successful radicand have the predicted natural density.
-/
@[category research solved, AMS 11,
  formal_proof using lean4 at
    "https://github.com/DomTheDeveloper/formal-conjectures/blob/796f5e8919a844d78e8bb683d1974e118aa263ee/FormalConjectures/OEIS/261865FinalAudit.lean"]
theorem density_formula (j : ℕ) (hj : 2 ≤ j) (hsq : Squarefree j) :
    {n : ℕ | 0 < n ∧ IsValue n j}.HasDensity (predictedDensity j) := by
  sorry

end OeisA261865
