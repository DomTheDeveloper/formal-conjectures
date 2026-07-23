import FormalConjecturesUtil

namespace WOWII59ResidueTest

open SimpleGraph

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def testG : SimpleGraph (Fin 18) where
  Adj u v := u ≠ v ∧ (u.val = 10 ∨ v.val = 10)
  symm u v h := ⟨h.1.symm, h.2.symm⟩
  loopless u h := h.1 rfl

instance : DecidableRel testG.Adj := fun u v => by
  unfold testG
  infer_instance

example : residue testG = 16 := by
  decide

end WOWII59ResidueTest
