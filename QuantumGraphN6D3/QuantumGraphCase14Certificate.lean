import QuantumGraphSemantic

/-! Reflected LRAT certificate for quantum-graph support orbit case 14. -/

open Std Sat
open Std.Tactic.BVDecide

namespace QuantumGraphCase14Certificate

open QuantumGraphSemantic
open QuantumGraphCompactLRAT

def mask : Nat := 0x421f
def caseCNF : CNF Nat := buildCaseCNF mask
def certificate : String :=
  include_str "certificates" / "case_14.clrat"

theorem case_unsat : caseCNF.Unsat := by
  apply verifyCompactCert_correct caseCNF certificate
  native_decide

theorem semantic_unsat : (semanticCaseCNF mask).Unsat := by
  rw [← CNF.unsat_relabel_iff (fun _ _ h => encodeVar_injective h)]
  have hencode : CNF.relabel encodeVar (semanticCaseCNF mask) = caseCNF := by
    native_decide
  rw [hencode]
  exact case_unsat

end QuantumGraphCase14Certificate
