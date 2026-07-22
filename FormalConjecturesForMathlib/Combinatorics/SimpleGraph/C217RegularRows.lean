/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217RegularCertificate

/-!
# The four regular boundary rows for WOWII Conjecture 217
-/

namespace SimpleGraph.C217RegularRows

open Classical
open SimpleGraph
open SimpleGraph.C217OrderBound
open SimpleGraph.C217RegularCertificate

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- The cubic row on eight vertices. -/
theorem row_33333333
    (cert : RegularCertificate 8 3)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G = [3,3,3,3,3,3,3,3]) :
    IsTraceable G := by
  apply isTraceable_of_regular_row_certificate (n := 8) (k := 3)
    (by norm_num) cert G hG
  simpa using hrow

/-- The four-regular row on ten vertices. -/
theorem row_4444444444
    (cert : RegularCertificate 10 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G = [4,4,4,4,4,4,4,4,4,4]) :
    IsTraceable G := by
  apply isTraceable_of_regular_row_certificate (n := 10) (k := 4)
    (by norm_num) cert G hG
  simpa using hrow

/-- The five-regular row on twelve vertices. -/
theorem row_555555555555
    (cert : RegularCertificate 12 5)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G = [5,5,5,5,5,5,5,5,5,5,5,5]) :
    IsTraceable G := by
  apply isTraceable_of_regular_row_certificate (n := 12) (k := 5)
    (by norm_num) cert G hG
  simpa using hrow

/-- The six-regular row on fourteen vertices. -/
theorem row_66666666666666
    (cert : RegularCertificate 14 6)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G = [6,6,6,6,6,6,6,6,6,6,6,6,6,6]) :
    IsTraceable G := by
  apply isTraceable_of_regular_row_certificate (n := 14) (k := 6)
    (by norm_num) cert G hG
  simpa using hrow

#print axioms SimpleGraph.C217RegularRows.row_33333333
#print axioms SimpleGraph.C217RegularRows.row_4444444444
#print axioms SimpleGraph.C217RegularRows.row_555555555555
#print axioms SimpleGraph.C217RegularRows.row_66666666666666

end SimpleGraph.C217RegularRows
