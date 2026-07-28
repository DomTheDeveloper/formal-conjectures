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

/-!
# Definitions for Ben Green's Open Problem 14

This file holds the shared van der Waerden definitions for Green's Problem 14
(`Green14.mixedMonoAPGuaranteeSet` and the 2-colour van der Waerden number
`Green14.W`), so that both the problem statement in
`FormalConjectures.GreensOpenProblems.«14»` and the certificate chain
(`Green14Core` through `Green14FastKernel20`) can depend on them without an
import cycle.
-/

open Set

namespace Green14

/--
The set of natural numbers $N$ such that any 2-coloring of ${1, ..., N}$ contains a monochromatic
arithmetic progression of length $k$ (color 0) or length $r$ (color 1).
-/
def mixedMonoAPGuaranteeSet (k r : ℕ) : Set ℕ :=
  { N | ∀ coloring : Icc 1 N → Fin 2,
    (∃ s : Finset (Icc 1 N), ({(s' : ℕ) | s' ∈ s}).IsAPOfLength k ∧ ∀ x ∈ s, coloring x = 0) ∨
    (∃ s : Finset (Icc 1 N), ({(s' : ℕ) | s' ∈ s}).IsAPOfLength r ∧ ∀ x ∈ s, coloring x = 1) }

/--
We define the 2-colour van der Waerden numbers $W(k, r)$ to be the least quantities such that if
$\{1, ... , W(k, r)\}$ is coloured red and blue then there is either a red $k$-term progression
or a blue $r$-term progression.
-/
noncomputable def W (k r : ℕ) : ℕ := sInf (mixedMonoAPGuaranteeSet k r)

end Green14
