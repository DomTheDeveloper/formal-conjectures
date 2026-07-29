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

import FormalConjectures.GreensOpenProblems.Green14FastKernel20

/-!
# Upper-order bridge for Green14

The computational upper-bound certificate only has to establish that `389`
belongs to the mixed monochromatic arithmetic-progression guarantee set. This
file converts that semantic fact into the numerical upper bound and combines it
with the existing kernel-checked lower-bound certificate.
-/

namespace Green14

/-- Membership of `N` in the guarantee set gives the corresponding upper bound
for the least guaranteed interval length. -/
theorem W_le_of_mem {k r N : ℕ}
    (hN : N ∈ mixedMonoAPGuaranteeSet k r) : W k r ≤ N := by
  rw [W]
  exact Nat.sInf_le hN

/-- The final exact value follows as soon as the upper-bound certificate proves
that every coloring of `{1, ..., 389}` has the required progression. -/
theorem W_3_20_eq_389_of_mem
    (h389 : 389 ∈ mixedMonoAPGuaranteeSet 3 20) : W 3 20 = 389 := by
  apply Nat.le_antisymm
  · exact W_le_of_mem h389
  · exact FastKernel.W_3_20_lower_fast

end Green14
