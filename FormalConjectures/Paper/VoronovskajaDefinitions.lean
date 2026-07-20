/-
Copyright 2025 The Formal Conjectures Authors.

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

-- Lean 4.27 normalized moment-limit verification trigger.
public import FormalConjectures.Util.ProblemImports

/-!
# Definitions for the Bézier variant of Bernstein operators

This lower-level module contains only the operator definitions, so proof infrastructure can be used
by the original Formal Conjectures theorem file without creating an import cycle.
-/

public section

noncomputable section

open Topology Filter Real unitInterval Polynomial

namespace VoronovskajaTypeFormula

/-- Cumulative Bernstein sum `J_{n,k}(x) = ∑_{j=k}^n p_{n,j}(x)`. -/
@[expose]
noncomputable def bernsteinTail (n k : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.Icc k n, bernsteinPolynomial ℝ n j

/-- Bézier-type Bernstein operator. -/
@[expose]
noncomputable def bezierBernstein (n : ℕ) (α : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    f ((k : ℝ) / (n : ℝ)) *
      ((bernsteinTail n k).eval x ^ α - (bernsteinTail n (k + 1)).eval x ^ α)

end VoronovskajaTypeFormula
