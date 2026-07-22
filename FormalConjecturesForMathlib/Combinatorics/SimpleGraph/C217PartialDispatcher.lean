/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217EasyRows
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217SeedRows
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217TwoStageRow
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217StagedSeedRows
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217FinalIrregularRow
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217TwoBlockRows
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217HighSeedRows
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217FiniteCertificate

/-!
# Partial exceptional dispatcher for WOWII Conjecture 217

Thirty of the forty certified exceptional degree rows are discharged here.
The remaining ten rows are listed explicitly: four regular boundary rows, the
`K_{4,6}` obstruction row, the order-eleven parity row, and four mixed
order-twelve closure rows.
-/

namespace SimpleGraph.C217PartialDispatcher

open Classical
open SimpleGraph
open SimpleGraph.C217OrderBound
open SimpleGraph.C217EasyRows
open SimpleGraph.C217SeedRows
open SimpleGraph.C217TwoStageRow
open SimpleGraph.C217StagedSeedRows
open SimpleGraph.C217FinalIrregularRow
open SimpleGraph.C217TwoBlockRows
open SimpleGraph.C217HighSeedRows
open SimpleGraph.C217FiniteCertificate

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- Handled rows outside the fifteen-row parametric two-block family. -/
def additionalHandledRows : List (List ℕ) :=
  [ [1,1,1,1],
    [2,2,2,2,2,2],
    [3,3,2,2,2,2],
    [4,4,4,3,3,3,3,2],
    [4,4,3,3,3,3,3,3],
    [5,4,4,3,3,3,3,3],
    [5,5,5,5,4,4,4,4,3,3],
    [5,5,5,4,4,4,4,4,4,3],
    [6,5,5,5,4,4,4,4,4,3],
    [5,5,4,4,4,4,4,4,4,4],
    [6,5,5,4,4,4,4,4,4,4],
    [5,5,5,5,4,4,4,4,4,4],
    [6,6,5,5,4,4,4,4,4,4],
    [6,6,5,5,5,5,5,5,5,5,5,5],
    [6,6,6,6,5,5,5,5,5,5,5,5] ]

/-- All thirty rows currently handled in source. -/
def handledRows : List (List ℕ) :=
  twoBlockRows ++ additionalHandledRows

/-- The exact ten-row formal remainder. -/
def remainingRows : List (List ℕ) :=
  [ [3,3,3,3,3,3,3,3],
    [4,4,4,4,4,4,4,4,4,4],
    [6,6,6,6,4,4,4,4,4,4],
    [6,6,6,6,5,5,4,4,4,4,4],
    [6,6,6,6,6,5,5,5,5,4,4,4],
    [6,6,6,6,5,5,5,5,5,5,4,4],
    [6,6,6,5,5,5,5,5,5,5,5,4],
    [6,6,6,6,6,5,5,5,5,5,5,4],
    [5,5,5,5,5,5,5,5,5,5,5,5],
    [6,6,6,6,6,6,6,6,6,6,6,6,6,6] ]

/-- Every certified exceptional row is either already handled or belongs to
the explicit ten-row remainder. -/
theorem exceptional_mem_handled_or_remaining
    {row : List ℕ} (hrow : row ∈ exceptionalSequences) :
    row ∈ handledRows ∨ row ∈ remainingRows := by
  simp only [exceptionalSequences, handledRows, twoBlockRows,
    additionalHandledRows, remainingRows, List.mem_append,
    List.mem_cons, List.mem_singleton] at hrow ⊢
  aesop

/-- Dispatcher for the fifteen nonparametric handled rows. -/
theorem isTraceable_of_mem_additionalHandledRows
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G ∈ additionalHandledRows) :
    IsTraceable G := by
  simp only [additionalHandledRows, List.mem_cons, List.mem_singleton] at hrow
  rcases hrow with hrow | hrow | hrow | hrow | hrow |
      hrow | hrow | hrow | hrow | hrow | hrow | hrow | hrow | hrow | hrow
  · exact row_1111 G hG hrow
  · exact row_222222 G hG hrow
  · exact row_332222 G hG hrow
  · exact row_44433332 G hG hrow
  · exact row_44333333 G hG hrow
  · exact row_54433333 G hG hrow
  · exact row_5555444433 G hG hrow
  · exact row_5554444443 G hG hrow
  · exact row_6555444443 G hG hrow
  · exact row_5544444444 G hrow
  · exact row_6554444444 G hrow
  · exact row_5555444444 G hrow
  · exact row_6655444444 G hrow
  · exact row_665555555555 G hrow
  · exact row_666655555555 G hrow

/-- All thirty handled exceptional rows are traceable. -/
theorem isTraceable_of_mem_handledRows
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hrow : degreeSequence G ∈ handledRows) :
    IsTraceable G := by
  rw [handledRows, List.mem_append] at hrow
  rcases hrow with htwo | hadd
  · exact isTraceable_of_mem_twoBlockRows G hG htwo
  · exact isTraceable_of_mem_additionalHandledRows G hG hadd

#print axioms SimpleGraph.C217PartialDispatcher.exceptional_mem_handled_or_remaining
#print axioms SimpleGraph.C217PartialDispatcher.isTraceable_of_mem_handledRows

end SimpleGraph.C217PartialDispatcher
