import QuantumGraphSemantic

/-! Reflected LRAT certificate for quantum-graph support orbit case 28. -/

open Std Sat
open Std.Tactic.BVDecide

namespace QuantumGraphCase28Certificate

open QuantumGraphSemantic
open QuantumGraphCompactLRAT

def mask : Nat := 0x0f67
def caseCNF : CNF Nat := buildCaseCNF mask
def certificate : String :=
  include_str "certificates" / "case_28.clrat"

theorem case_unsat : caseCNF.Unsat := by
  apply verifyCompactCert_correct caseCNF certificate
  native_decide

theorem semantic_unsat : (semanticCaseCNF mask).Unsat := by
  rw [← CNF.unsat_relabel_iff (fun _ _ h => encodeVar_injective h)]
  have hencode : CNF.relabel encodeVar (semanticCaseCNF mask) = caseCNF := by
    native_decide
  rw [hencode]
  exact case_unsat

end QuantumGraphCase28Certificate
