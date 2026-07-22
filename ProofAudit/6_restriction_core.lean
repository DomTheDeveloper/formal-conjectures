import FormalConjectures.Paper.MonochromaticQuantumGraph
import Mathlib.Tactic.BVDecide
import Mathlib.Data.BitVec

open MonochromaticQuantumGraph

namespace QuantumD3Experiment

example : (1 : BitVec 1) + 1 = 0 := by native_decide

example (x y : BitVec 1) : x + y = y + x := by bv_decide

example (w : BitVec 16) :
    BitVec.ofBool (w.getLsbD 0) * BitVec.ofBool (w.getLsbD 1) =
      BitVec.ofBool (w.getLsbD 1) * BitVec.ofBool (w.getLsbD 0) := by
  bv_decide

end QuantumD3Experiment
