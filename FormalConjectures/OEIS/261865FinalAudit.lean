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

import FormalConjectures.OEIS.«261865»

namespace OeisA261865

/-- Exact-statement audit wrapper for Peter Kagey's Problem 13 / OEIS A261865. -/
theorem density_formula_final_audit (j : ℕ) (hj : 2 ≤ j) (hsq : Squarefree j) :
    {n : ℕ | 0 < n ∧ IsValue n j}.HasDensity (predictedDensity j) :=
  density_formula j hj hsq

#print axioms density_formula_solution
#print axioms density_formula
#print axioms density_formula_final_audit

end OeisA261865
