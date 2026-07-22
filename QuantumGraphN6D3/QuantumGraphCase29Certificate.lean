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

import QuantumGraphSemantic

/-! Reflected LRAT certificate for quantum-graph support orbit case 29. -/

open Std Sat
open Std.Tactic.BVDecide

namespace QuantumGraphCase29Certificate

open QuantumGraphSemantic
open QuantumGraphCompactLRAT

def mask : Nat := 0x4b67
def caseCNF : CNF Nat := buildCaseCNF mask
def certificate : String :=
  include_str "certificates" / "case_29.clrat"

theorem case_unsat : caseCNF.Unsat := by
  apply verifyCompactCert_correct caseCNF certificate
  native_decide

theorem semantic_unsat : (semanticCaseCNF mask).Unsat := by
  rw [← CNF.unsat_relabel_iff (fun _ _ h => encodeVar_injective h)]
  have hencode : CNF.relabel encodeVar (semanticCaseCNF mask) = caseCNF := by
    native_decide
  rw [hencode]
  exact case_unsat

end QuantumGraphCase29Certificate
