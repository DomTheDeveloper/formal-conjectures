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

import FormalConjectures.GreensOpenProblems.Green14FunctionCertificateBridge

/-!
# Fast kernel proof for the Green14 t=20 certificate

The 388-point coloring is represented by a single natural-number bit mask:
a set bit marks color `0`, and an unset bit marks color `1`. This avoids
repeated kernel normalization of a 388-entry array literal while retaining a
fully proof-producing `decide` check.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Green14.FastKernel

private def zeroMask20 : Nat :=
  0x1001080a10004010a00063401000020085044008000402000100220a10040000802c6000508020008501080080000

private def color20 (i : Nat) : Bool := !(zeroMask20.testBit i)

open Green14.FunctionCertificateBridge

theorem valid_20 :
    hasAP 388 3 color20 false = false ∧
      hasAP 388 20 color20 true = false := by
  decide

/-- Kernel-clean proof of the recorded lower bound `W(3,20) ≥ 389`. -/
theorem W_3_20_lower_fast : Green14.W 3 20 ≥ 389 := by
  exact W_ge_succ_of_checks (N := 388) (r := 20) (by omega) valid_20

#print axioms Green14.FastKernel.valid_20
#print axioms Green14.FastKernel.W_3_20_lower_fast

end Green14.FastKernel
