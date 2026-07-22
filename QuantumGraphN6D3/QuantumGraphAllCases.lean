import QuantumGraphOrbitBridge
import QuantumGraphCase01Certificate
import QuantumGraphCase02Certificate
import QuantumGraphCase03Certificate
import QuantumGraphCase04Certificate
import QuantumGraphCase05Certificate
import QuantumGraphCase06Certificate
import QuantumGraphCase07Certificate
import QuantumGraphCase08Certificate
import QuantumGraphCase09Certificate
import QuantumGraphCase10Certificate
import QuantumGraphCase11Certificate
import QuantumGraphCase12Certificate
import QuantumGraphCase13Certificate
import QuantumGraphCase14Certificate
import QuantumGraphCase15Certificate
import QuantumGraphCase16Certificate
import QuantumGraphCase17Certificate
import QuantumGraphCase18Certificate
import QuantumGraphCase19Certificate
import QuantumGraphCase20Certificate
import QuantumGraphCase21Certificate
import QuantumGraphCase22Certificate
import QuantumGraphCase23Certificate
import QuantumGraphCase24Certificate
import QuantumGraphCase25Certificate
import QuantumGraphCase26Certificate
import QuantumGraphCase27Certificate
import QuantumGraphCase28Certificate
import QuantumGraphCase29Certificate
import QuantumGraphCase30Certificate
import QuantumGraphCase31Certificate
import QuantumGraphCase32Certificate
import QuantumGraphCase33Certificate
import QuantumGraphCase34Certificate
import QuantumGraphCase35Certificate
import QuantumGraphCase36Certificate
import QuantumGraphCase37Certificate
import QuantumGraphCase38Certificate
import QuantumGraphCase39Certificate
import QuantumGraphCase40Certificate
import QuantumGraphCase41Certificate
import QuantumGraphCase42Certificate
import QuantumGraphCase43Certificate
import QuantumGraphCase44Certificate
import QuantumGraphCase45Certificate
import QuantumGraphCase46Certificate

/-!
# Exhaustive reflected certificates for the 47 odd-support orbits
-/

open Std Sat

namespace QuantumGraphAllCases

open QuantumGraphSemantic QuantumGraphOrbitBridge QuantumGraphOrbitData

def representativeNats : Array Nat := #[
  0x4024, 0x5030, 0x2461, 0x4261, 0x5211, 0x7308, 0x14b8, 0x24e2, 0x206e, 0x1278, 0x1329, 0x226e, 0x4f81, 0x4267, 0x421f, 0x13a9, 0x228f, 0x132d, 0x5235, 0x7027, 0x226f, 0x13e9, 0x52e9, 0x7aa2, 0x4277, 0x5e31, 0x7329, 0x1b39, 0x0f67, 0x4b67, 0x51f3, 0x427f, 0x333d, 0x527e, 0x1b3d, 0x16fd, 0x73e9, 0x1bbb, 0x7b39, 0x5773, 0x17ef, 0x56fd, 0x79f3, 0x5fb5, 0x7f9b, 0x57ff, 0x7fff
]

theorem representativeMask_toNat (caseIndex : Fin 47) :
    (representativeMask caseIndex).toNat = representativeNats[caseIndex.val]! := by
  native_decide +revert

theorem representative_semantic_unsat (caseIndex : Fin 47) :
    (semanticCaseCNF (representativeMask caseIndex).toNat).Unsat := by
  rw [representativeMask_toNat]
  fin_cases caseIndex
  · simpa [representativeNats] using semantic_case00_unsat
  · simpa [representativeNats, QuantumGraphCase01Certificate.mask] using
      QuantumGraphCase01Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase02Certificate.mask] using
      QuantumGraphCase02Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase03Certificate.mask] using
      QuantumGraphCase03Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase04Certificate.mask] using
      QuantumGraphCase04Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase05Certificate.mask] using
      QuantumGraphCase05Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase06Certificate.mask] using
      QuantumGraphCase06Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase07Certificate.mask] using
      QuantumGraphCase07Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase08Certificate.mask] using
      QuantumGraphCase08Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase09Certificate.mask] using
      QuantumGraphCase09Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase10Certificate.mask] using
      QuantumGraphCase10Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase11Certificate.mask] using
      QuantumGraphCase11Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase12Certificate.mask] using
      QuantumGraphCase12Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase13Certificate.mask] using
      QuantumGraphCase13Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase14Certificate.mask] using
      QuantumGraphCase14Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase15Certificate.mask] using
      QuantumGraphCase15Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase16Certificate.mask] using
      QuantumGraphCase16Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase17Certificate.mask] using
      QuantumGraphCase17Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase18Certificate.mask] using
      QuantumGraphCase18Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase19Certificate.mask] using
      QuantumGraphCase19Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase20Certificate.mask] using
      QuantumGraphCase20Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase21Certificate.mask] using
      QuantumGraphCase21Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase22Certificate.mask] using
      QuantumGraphCase22Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase23Certificate.mask] using
      QuantumGraphCase23Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase24Certificate.mask] using
      QuantumGraphCase24Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase25Certificate.mask] using
      QuantumGraphCase25Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase26Certificate.mask] using
      QuantumGraphCase26Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase27Certificate.mask] using
      QuantumGraphCase27Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase28Certificate.mask] using
      QuantumGraphCase28Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase29Certificate.mask] using
      QuantumGraphCase29Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase30Certificate.mask] using
      QuantumGraphCase30Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase31Certificate.mask] using
      QuantumGraphCase31Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase32Certificate.mask] using
      QuantumGraphCase32Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase33Certificate.mask] using
      QuantumGraphCase33Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase34Certificate.mask] using
      QuantumGraphCase34Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase35Certificate.mask] using
      QuantumGraphCase35Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase36Certificate.mask] using
      QuantumGraphCase36Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase37Certificate.mask] using
      QuantumGraphCase37Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase38Certificate.mask] using
      QuantumGraphCase38Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase39Certificate.mask] using
      QuantumGraphCase39Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase40Certificate.mask] using
      QuantumGraphCase40Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase41Certificate.mask] using
      QuantumGraphCase41Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase42Certificate.mask] using
      QuantumGraphCase42Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase43Certificate.mask] using
      QuantumGraphCase43Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase44Certificate.mask] using
      QuantumGraphCase44Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase45Certificate.mask] using
      QuantumGraphCase45Certificate.semantic_unsat
  · simpa [representativeNats, QuantumGraphCase46Certificate.mask] using
      QuantumGraphCase46Certificate.semantic_unsat

end QuantumGraphAllCases
