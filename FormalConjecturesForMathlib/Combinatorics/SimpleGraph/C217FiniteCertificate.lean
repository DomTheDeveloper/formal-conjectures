/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217OrderCertificate
import Mathlib.Tactic.IntervalCases

/-!
# Finite degree-sequence certificate for WOWII Conjecture 217

This file records the deterministic exceptional rows and also checks the
stronger exhaustive statement: every positive bounded residue-two sequence of
orders two through fourteen either satisfies the count-form Chvátal condition
or is one of the forty rows.
-/

namespace SimpleGraph.C217FiniteCertificate

open C217OrderCertificate

/-- Proof families used by the mathematical and no-Graffiti proofs. -/
inductive ProofFamily
  | impossibleConnected
  | regularBoundary
  | parametricTwoBlockClosure
  | lowSeedCompletion
  | lowTwoStageCompletion
  | highDeltaClosure
  | highDeltaLeafObstruction
  deriving DecidableEq, Repr

abbrev Row := List ℕ × ProofFamily

/-- All exceptional degree sequences. Lists are stored in descending order. -/
def rows : List Row :=
  [ ([1, 1, 1, 1], .impossibleConnected)
  , ([2, 2, 2, 1, 1], .parametricTwoBlockClosure)
  , ([3, 3, 3, 3, 1, 1], .parametricTwoBlockClosure)
  , ([2, 2, 2, 2, 2, 2], .regularBoundary)
  , ([3, 3, 2, 2, 2, 2], .lowSeedCompletion)
  , ([4, 4, 4, 4, 4, 1, 1], .parametricTwoBlockClosure)
  , ([3, 3, 3, 3, 2, 2, 2], .parametricTwoBlockClosure)
  , ([5, 5, 5, 5, 5, 5, 1, 1], .parametricTwoBlockClosure)
  , ([4, 4, 4, 4, 4, 2, 2, 2], .parametricTwoBlockClosure)
  , ([4, 4, 4, 3, 3, 3, 3, 2], .lowSeedCompletion)
  , ([3, 3, 3, 3, 3, 3, 3, 3], .regularBoundary)
  , ([4, 4, 3, 3, 3, 3, 3, 3], .lowSeedCompletion)
  , ([5, 4, 4, 3, 3, 3, 3, 3], .lowSeedCompletion)
  , ([6, 6, 6, 6, 6, 6, 6, 1, 1], .parametricTwoBlockClosure)
  , ([5, 5, 5, 5, 5, 5, 2, 2, 2], .parametricTwoBlockClosure)
  , ([4, 4, 4, 4, 4, 3, 3, 3, 3], .parametricTwoBlockClosure)
  , ([6, 6, 6, 6, 6, 6, 6, 2, 2, 2], .parametricTwoBlockClosure)
  , ([5, 5, 5, 5, 5, 5, 3, 3, 3, 3], .parametricTwoBlockClosure)
  , ([5, 5, 5, 5, 4, 4, 4, 4, 3, 3], .lowSeedCompletion)
  , ([5, 5, 5, 4, 4, 4, 4, 4, 4, 3], .lowTwoStageCompletion)
  , ([6, 5, 5, 5, 4, 4, 4, 4, 4, 3], .lowSeedCompletion)
  , ([4, 4, 4, 4, 4, 4, 4, 4, 4, 4], .regularBoundary)
  , ([5, 5, 4, 4, 4, 4, 4, 4, 4, 4], .highDeltaClosure)
  , ([6, 5, 5, 4, 4, 4, 4, 4, 4, 4], .highDeltaClosure)
  , ([5, 5, 5, 5, 4, 4, 4, 4, 4, 4], .highDeltaClosure)
  , ([6, 6, 5, 5, 4, 4, 4, 4, 4, 4], .highDeltaClosure)
  , ([6, 6, 6, 6, 4, 4, 4, 4, 4, 4], .highDeltaLeafObstruction)
  , ([6, 6, 6, 6, 6, 6, 6, 3, 3, 3, 3], .parametricTwoBlockClosure)
  , ([5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4], .parametricTwoBlockClosure)
  , ([6, 6, 6, 6, 5, 5, 4, 4, 4, 4, 4], .highDeltaClosure)
  , ([6, 6, 6, 6, 6, 6, 6, 4, 4, 4, 4, 4], .parametricTwoBlockClosure)
  , ([6, 6, 6, 6, 6, 5, 5, 5, 5, 4, 4, 4], .highDeltaClosure)
  , ([6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 4, 4], .highDeltaClosure)
  , ([6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 4], .highDeltaClosure)
  , ([6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 4], .highDeltaClosure)
  , ([5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5], .regularBoundary)
  , ([6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5], .highDeltaClosure)
  , ([6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5], .highDeltaClosure)
  , ([6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5], .parametricTwoBlockClosure)
  , ([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6], .regularBoundary)
  ]

/-- The underlying exceptional sequences without their proof-family tags. -/
def exceptionalSequences : List (List ℕ) := rows.map Prod.fst

/-- Minimum entry of a descending nonempty sequence, with zero as fallback. -/
def minEntry (s : List ℕ) : ℕ := s.reverse.headD 0

/-- The direct proof uses exactly the rows of minimum degree at most three. -/
def directRows : List Row := rows.filter fun r => minEntry r.1 ≤ 3

/-- Original indexed Boolean form of Chvátal's path criterion. -/
def chvatalPathHolds (desc : List ℕ) : Bool :=
  let asc := desc.reverse
  let n := asc.length
  (List.range (n + 1)).all fun i =>
    if 1 ≤ i ∧ 2 * i < n + 1 then
      decide (i ≤ asc.getD (i - 1) 0 ∨ n - i ≤ asc.getD (n - i) 0)
    else true

/-- Count form of Chvátal's criterion, suited to graph degree filters. -/
def chvatalCountHolds (desc : List ℕ) : Bool :=
  let n := desc.length
  (List.range (n + 1)).all fun i =>
    if 1 ≤ i ∧ 2 * i < n + 1 then
      decide ((desc.countP fun d => decide (d < i)) < i ∨
        (desc.countP fun d => decide (d < n - i)) ≤ n - i)
    else true

/-- The exhaustive finite classification predicate. -/
def classified (desc : List ℕ) : Bool :=
  if desc.all (fun d => decide (1 ≤ d)) && residueAux desc == 2 then
    chvatalCountHolds desc || decide (desc ∈ exceptionalSequences)
  else true

/-- Every listed row has Havel--Hakimi residue two. -/
theorem rows_residue_two : rows.all (fun r => residueAux r.1 == 2) = true := by
  decide

/-- Every listed row fails the indexed Chvátal criterion. -/
theorem rows_fail_chvatal : rows.all (fun r => !(chvatalPathHolds r.1)) = true := by
  decide

/-- Every listed row also fails the count-form Chvátal criterion. -/
theorem rows_fail_chvatal_count :
    rows.all (fun r => !(chvatalCountHolds r.1)) = true := by
  decide

/-- The no-Graffiti fallback has forty rows. -/
theorem rows_length : rows.length = 40 := by decide

/-- The direct proof has twenty-two low-minimum-degree rows. -/
theorem directRows_length : directRows.length = 22 := by decide

/-- All entries are positive and at most six. -/
theorem rows_degree_bounds :
    rows.all (fun r => r.1.all (fun d => decide (1 ≤ d ∧ d ≤ 6))) = true := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Exhaustive classification for each possible graph order. -/
theorem classify_order_2 : ∀ m : Sym (Fin 7) 2, classified (degreeList m) = true := by decide
set_option maxHeartbeats 0 in theorem classify_order_3 : ∀ m : Sym (Fin 7) 3, classified (degreeList m) = true := by decide
set_option maxHeartbeats 0 in theorem classify_order_4 : ∀ m : Sym (Fin 7) 4, classified (degreeList m) = true := by decide
set_option maxHeartbeats 0 in theorem classify_order_5 : ∀ m : Sym (Fin 7) 5, classified (degreeList m) = true := by decide
set_option maxHeartbeats 0 in theorem classify_order_6 : ∀ m : Sym (Fin 7) 6, classified (degreeList m) = true := by decide
set_option maxHeartbeats 0 in theorem classify_order_7 : ∀ m : Sym (Fin 7) 7, classified (degreeList m) = true := by decide
set_option maxHeartbeats 0 in theorem classify_order_8 : ∀ m : Sym (Fin 7) 8, classified (degreeList m) = true := by decide
set_option maxHeartbeats 0 in theorem classify_order_9 : ∀ m : Sym (Fin 7) 9, classified (degreeList m) = true := by decide
set_option maxHeartbeats 0 in theorem classify_order_10 : ∀ m : Sym (Fin 7) 10, classified (degreeList m) = true := by decide
set_option maxHeartbeats 0 in theorem classify_order_11 : ∀ m : Sym (Fin 7) 11, classified (degreeList m) = true := by decide
set_option maxHeartbeats 0 in theorem classify_order_12 : ∀ m : Sym (Fin 7) 12, classified (degreeList m) = true := by decide
set_option maxHeartbeats 0 in theorem classify_order_13 : ∀ m : Sym (Fin 7) 13, classified (degreeList m) = true := by decide
set_option maxHeartbeats 0 in theorem classify_order_14 : ∀ m : Sym (Fin 7) 14, classified (degreeList m) = true := by decide

/-- Uniform dispatcher for the thirteen bounded graph orders used by C217. -/
theorem classify_order_two_to_fourteen {n : ℕ} (h2 : 2 ≤ n) (h14 : n ≤ 14)
    (m : Sym (Fin 7) n) : classified (degreeList m) = true := by
  interval_cases n <;>
    first
    | exact classify_order_2 m
    | exact classify_order_3 m
    | exact classify_order_4 m
    | exact classify_order_5 m
    | exact classify_order_6 m
    | exact classify_order_7 m
    | exact classify_order_8 m
    | exact classify_order_9 m
    | exact classify_order_10 m
    | exact classify_order_11 m
    | exact classify_order_12 m
    | exact classify_order_13 m
    | exact classify_order_14 m

#print axioms SimpleGraph.C217FiniteCertificate.rows_residue_two
#print axioms SimpleGraph.C217FiniteCertificate.rows_fail_chvatal_count
#print axioms SimpleGraph.C217FiniteCertificate.rows_length
#print axioms SimpleGraph.C217FiniteCertificate.directRows_length
#print axioms SimpleGraph.C217FiniteCertificate.rows_degree_bounds
#print axioms SimpleGraph.C217FiniteCertificate.classify_order_14
#print axioms SimpleGraph.C217FiniteCertificate.classify_order_two_to_fourteen

end SimpleGraph.C217FiniteCertificate
