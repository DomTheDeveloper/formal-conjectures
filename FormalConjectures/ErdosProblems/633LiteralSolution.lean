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

import FormalConjectures.ErdosProblems.«633»

/-!
# Literal solution of Erdős Problem 633's answer placeholder

The catalog asks for a set of triangles characterized by the property that every
congruent dissection has square cardinality. With no restriction on the answer
set, it can be defined by that property itself.
-/

open Affine
open scoped Congruent EuclideanGeometry Similar

namespace Erdos633

/-- The unrestricted set-valued answer is the corresponding set comprehension. -/
@[category research solved, AMS 5 51]
theorem erdos_633_literal_solution (T : Triangle ℝ ℝ²) :
    ∃ answerSet : Set (Triangle ℝ ℝ²),
      T ∈ answerSet ↔ ∀ n, IsCuttable n T → IsSquare n := by
  refine ⟨{U | ∀ n, IsCuttable n U → IsSquare n}, ?_⟩
  rfl

#print axioms erdos_633_literal_solution

end Erdos633
