/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Residue

/-!
# Finite degree-sequence certificate for WOWII Conjecture 217

This file records the deterministic output of `scripts/c217_certificate.py` in a
small kernel-reducible form. It does not by itself prove traceability of every
row; it certifies the exact finite remainder and its proof-family partition.
-/

namespace SimpleGraph.C217FiniteCertificate

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

/-- All positive graphical degree sequences of order at most fourteen, maximum
entry at most six, Havel--Hakimi residue two, and failure of Chvátal's path
criterion. Lists are stored in descending order. -/
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

/-- Minimum entry of a descending nonempty sequence, with zero as the empty
fallback. -/
def minEntry (s : List ℕ) : ℕ := s.reverse.headD 0

/-- The direct proof uses exactly the rows of minimum degree at most three. -/
def directRows : List Row := rows.filter fun r => minEntry r.1 ≤ 3

/-- Boolean Chvátal path criterion for a descending sequence. -/
def chvatalPathHolds (desc : List ℕ) : Bool :=
  let asc := desc.reverse
  let n := asc.length
  (List.range (n + 1)).all fun i =>
    if 1 ≤ i ∧ 2 * i < n + 1 then
      decide (i ≤ asc.getD (i - 1) 0 ∨ n - i ≤ asc.getD (n - i) 0)
    else true

/-- Every listed row has Havel--Hakimi residue two. -/
theorem rows_residue_two : rows.all (fun r => residueAux r.1 == 2) = true := by
  decide

/-- Every listed row fails Chvátal's path criterion. -/
theorem rows_fail_chvatal : rows.all (fun r => !(chvatalPathHolds r.1)) = true := by
  decide

/-- The no-Graffiti fallback has forty rows. -/
theorem rows_length : rows.length = 40 := by
  decide

/-- The direct proof has twenty-two low-minimum-degree rows. -/
theorem directRows_length : directRows.length = 22 := by
  decide

/-- All entries are positive and at most six. -/
theorem rows_degree_bounds :
    rows.all (fun r => r.1.all (fun d => decide (1 ≤ d ∧ d ≤ 6))) = true := by
  decide

#print axioms SimpleGraph.C217FiniteCertificate.rows_residue_two
#print axioms SimpleGraph.C217FiniteCertificate.rows_fail_chvatal
#print axioms SimpleGraph.C217FiniteCertificate.rows_length
#print axioms SimpleGraph.C217FiniteCertificate.directRows_length
#print axioms SimpleGraph.C217FiniteCertificate.rows_degree_bounds

end SimpleGraph.C217FiniteCertificate
