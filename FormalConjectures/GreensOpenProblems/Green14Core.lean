/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Core definitions for Ben Green's Open Problem 14

This dependency-light module lets finite certificate proofs use the exact
catalog definitions without importing the catalog theorem file back into
itself. The separate kernel audit reuses these definitions with twenty direct
Boolean arrays, avoiding any native-evaluation trust assumption.
-/

open Filter Set Topology

namespace Green14

/-- The set of natural numbers `N` such that every two-coloring of
`{1, ..., N}` contains a color-0 `k`-term AP or a color-1 `r`-term AP. -/
def mixedMonoAPGuaranteeSet (k r : ℕ) : Set ℕ :=
  { N | ∀ coloring : Icc 1 N → Fin 2,
    (∃ s : Finset (Icc 1 N), ({(s' : ℕ) | s' ∈ s}).IsAPOfLength k ∧
      ∀ x ∈ s, coloring x = 0) ∨
    (∃ s : Finset (Icc 1 N), ({(s' : ℕ) | s' ∈ s}).IsAPOfLength r ∧
      ∀ x ∈ s, coloring x = 1) }

/-- The mixed two-color van der Waerden number. -/
noncomputable def W (k r : ℕ) : ℕ := sInf (mixedMonoAPGuaranteeSet k r)

end Green14
