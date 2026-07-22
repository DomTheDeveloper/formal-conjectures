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

public import FormalConjectures.OEIS.«261865Solution»

@[expose] public section

/-!
# OEIS A261865 / Peter Kagey's Problem 13

For a positive integer `n`, OEIS A261865 is the least positive integer `k`
for which a positive integer multiple of `√k` lies strictly between `n` and
`n + 1`.

For every squarefree `j ≥ 2`, the indices where `j` is the least successful
radicand have density

`(1 / √j) * ∏_{2 ≤ s < j, Squarefree s} (1 - 1 / √s)`.
-/

namespace OeisA261865

/--
**Peter Kagey's Problem 13 / OEIS A261865.**

For every squarefree `j ≥ 2`, the set of positive indices where the least
successful radicand is `j` has the stated natural density.

The mathematical proof and Lean development were produced by
ProofOrchestrator, using OpenAI GPT-5.6 Thinking, under Dominic Dabish's
supervision.
-/
@[category research, AMS 11]
theorem density_formula (j : ℕ) (hj : 2 ≤ j) (hsq : Squarefree j) :
    {n : ℕ | 0 < n ∧ IsValue n j}.HasDensity (predictedDensity j) :=
  density_formula_solution j hj hsq

end OeisA261865
