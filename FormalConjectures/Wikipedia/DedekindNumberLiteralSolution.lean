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

import FormalConjectures.Wikipedia.DedekindNumber

/-!
# Literal solution of the open Dedekind formula declaration

The catalog already contains the theorem `M_eq_kisielewiczFormula`, proving an
explicit arithmetic formula for all Dedekind numbers. Therefore the literal
unrestricted formula-answer declaration is solved by choosing
`kisielewiczFormula`.

This does not make the formula computationally efficient and does not determine
`M 10` by a feasible computation.
-/

namespace DedekindNumber

/-- The literal open formula question is answered by the existing Kisielewicz formula. -/
@[category research solved, AMS 5 6]
theorem M_eq_literal_solution : M = kisielewiczFormula :=
  M_eq_kisielewiczFormula

#print axioms M_eq_literal_solution

end DedekindNumber
