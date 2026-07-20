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

public import FormalConjectures.GreensOpenProblems.Green14ArrayCertificateBridge

/-!
# Fast kernel proof for the Green14 t=20 certificate

The coloring is stored as a Boolean array and the admissible-difference checker
is reduced by the Lean kernel.  The generic array reflection bridge then proves
the actual catalog inequality `W(3,20) ≥ 389`, without `native_decide`.
-/

public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Green14.FastKernel

private def colors20 : Array Bool :=
  #[
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false,
    true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, true,
    true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true,
    true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true,
    false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, false, false, true, true, true, false, false, true, false, true, true, true, true, true, true,
    true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true,
    false, true, true, true, true, false, true, false, true, true, true, true, true, false, true, true,
    true, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true,
    true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true,
    true, true, false, true, true, true, false, true, true, true, true, true, false, true, false, true,
    true, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true,
    true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, false, true, false, true, true, true, true, false, true, true, true, true, true, true, true,
    true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true,
    false, true, true, true, true, false, true, false, true, true, true, true, true, true, true, false,
    true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true,
    false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true
  ]

open Green14.ArrayCertificateBridge

theorem valid_20 :
    hasAP 388 3 colors20 false = false ∧
      hasAP 388 20 colors20 true = false := by
  decide

/-- Kernel-clean proof of the recorded lower bound `W(3,20) ≥ 389`. -/
theorem W_3_20_lower_fast : Green14.W 3 20 ≥ 389 := by
  exact W_ge_succ_of_checks (N := 388) (r := 20) (by omega) valid_20

#print axioms Green14.FastKernel.valid_20
#print axioms Green14.FastKernel.W_3_20_lower_fast

end Green14.FastKernel
