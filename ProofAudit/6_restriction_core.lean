import FormalConjectures.Paper.MonochromaticQuantumGraph
import Mathlib.Tactic.BVDecide
import Mathlib.Data.BitVec

/-!
# Exact characteristic-two obstruction for N = 6, D = 3

The 15 unordered vertex pairs each carry a 3 by 3 table of one-bit weights,
for 135 Boolean variables in total.  For each of the 3^6 inherited vertex
colourings, `pm6` is the parity of the 15 perfect-matching monomials.
-/

namespace QuantumD3Experiment

abbrev F2 := BitVec 1
abbrev PackedWeights := BitVec 135

/-- Lexicographic slot for an unordered pair `u < v` in `Fin 6`. -/
def pairSlot (u v : Nat) : Nat :=
  if u = 0 then v - 1
  else if u = 1 then 5 + (v - 2)
  else if u = 2 then 9 + (v - 3)
  else if u = 3 then 12 + (v - 4)
  else 14

/-- One of the 135 relevant weights. -/
def wt (w : PackedWeights) (u v i j : Nat) : F2 :=
  BitVec.ofBool (w.getLsbD (9 * pairSlot u v + 3 * i + j))

/-- Product contributed by one perfect matching. -/
def mterm (w : PackedWeights)
    (u v x y p q : Nat) (a b c d e f : Nat) : F2 :=
  let col : Nat → Nat
    | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | _ => f
  wt w u v (col u) (col v) *
    wt w x y (col x) (col y) *
    wt w p q (col p) (col q)

/-- The parity of the 15 perfect matchings of `K₆`. -/
def pm6 (w : PackedWeights) (a b c d e f : Nat) : F2 :=
    mterm w 0 1 2 3 4 5 a b c d e f
  + mterm w 0 1 2 4 3 5 a b c d e f
  + mterm w 0 1 2 5 3 4 a b c d e f
  + mterm w 0 2 1 3 4 5 a b c d e f
  + mterm w 0 2 1 4 3 5 a b c d e f
  + mterm w 0 2 1 5 3 4 a b c d e f
  + mterm w 0 3 1 2 4 5 a b c d e f
  + mterm w 0 3 1 4 2 5 a b c d e f
  + mterm w 0 3 1 5 2 4 a b c d e f
  + mterm w 0 4 1 2 3 5 a b c d e f
  + mterm w 0 4 1 3 2 5 a b c d e f
  + mterm w 0 4 1 5 2 3 a b c d e f
  + mterm w 0 5 1 2 3 4 a b c d e f
  + mterm w 0 5 1 3 2 4 a b c d e f
  + mterm w 0 5 1 4 2 3 a b c d e f

/-- One equation of the system, returned as a Boolean. -/
def checkTuple (w : PackedWeights) (a b c d e f : Nat) : Bool :=
  let mono := (a == b) && (b == c) && (c == d) && (d == e) && (e == f)
  pm6 w a b c d e f == if mono then (1 : F2) else 0

/-- All `3^6 = 729` equations. -/
def checkAll (w : PackedWeights) : Bool :=
  (List.range 3).all fun a =>
  (List.range 3).all fun b =>
  (List.range 3).all fun c =>
  (List.range 3).all fun d =>
  (List.range 3).all fun e =>
  (List.range 3).all fun f => checkTuple w a b c d e f

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- No assignment of the 135 relevant one-bit weights satisfies the N=6, D=3
monochromatic perfect-matching equation system. -/
theorem no_packed_solution (w : PackedWeights) : checkAll w = false := by
  bv_decide

#print axioms no_packed_solution

end QuantumD3Experiment
