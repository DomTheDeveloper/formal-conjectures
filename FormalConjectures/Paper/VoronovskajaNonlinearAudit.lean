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

import FormalConjectures.Paper.VoronovskajaTypeFormula

/-!
# Nonlinear Voronovskaja kernel audit

This file deliberately imports only the exact Formal Conjectures declaration and prints the axioms
of the nonlinear theorem and its terminal dependency. It is independent of the classical
`α = 1` formalization.
-/

#print axioms VoronovskajaTypeFormula.voronovskaja_theorem.bezier_bernstein_operators
#print axioms VoronovskajaTypeFormula.tendsto_bezierBernstein_all
