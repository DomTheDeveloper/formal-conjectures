/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217RowFacts
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.DegreeTwoTraceable
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.ConeHamiltonian

/-!
# Easy exceptional rows for WOWII Conjecture 217

Three rows in the forty-row certificate have maximum degree at most two. They
are discharged uniformly by the connected maximum-degree-two traceability
theorem; no realization classification is required.
-/

namespace SimpleGraph.C217EasyRows

open Classical
open SimpleGraph.C217OrderBound
open SimpleGraph.C217RowFacts

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- Any exact degree row bounded by two is traceable in a connected graph. -/
theorem isTraceable_of_degreeSequence_eq_of_all_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    {row : List ℕ} (hrow : degreeSequence G = row)
    (hbound : ∀ d ∈ row, d ≤ 2) :
    IsTraceable G := by
  exact hG.exists_hamiltonianPath_of_degree_le_two G
    (degree_le_of_degreeSequence_eq G hrow hbound)

/-- The formally impossible connected row `[1,1,1,1]` is harmless: any
connected realization would already be traceable by the degree-two theorem. -/
theorem row_1111
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G = [1, 1, 1, 1]) :
    IsTraceable G := by
  apply isTraceable_of_degreeSequence_eq_of_all_le_two G hG hrow
  simp

/-- The row `[2,2,2,1,1]` is traceable. -/
theorem row_22211
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G = [2, 2, 2, 1, 1]) :
    IsTraceable G := by
  apply isTraceable_of_degreeSequence_eq_of_all_le_two G hG hrow
  simp

/-- The regular row `[2,2,2,2,2,2]` is traceable. -/
theorem row_222222
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G = [2, 2, 2, 2, 2, 2]) :
    IsTraceable G := by
  apply isTraceable_of_degreeSequence_eq_of_all_le_two G hG hrow
  simp

#print axioms SimpleGraph.C217EasyRows.row_1111
#print axioms SimpleGraph.C217EasyRows.row_22211
#print axioms SimpleGraph.C217EasyRows.row_222222

end SimpleGraph.C217EasyRows
