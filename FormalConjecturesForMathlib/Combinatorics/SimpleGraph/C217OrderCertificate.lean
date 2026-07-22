/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Residue

/-!
# Kernel-computable order certificate for WOWII Conjecture 217

`boundedSortedLists k n` enumerates all descending lists of length `n` whose
entries are at most `k`. The two terminal checks below prove computationally:

* no such list of length sixteen and maximum entry six has residue two;
* every such list of length fifteen with residue two has odd sum.

The graph-theoretic bridge uses sortedness of the graph degree sequence and the
handshake parity law. The general completeness lemmas for the enumerator are
kept separate from these finite kernel checks.
-/

namespace SimpleGraph.C217OrderCertificate

/-- All descending lists of length `n` with entries in `0, ..., k`. The number
of copies of `k` is selected first, followed recursively by entries below `k`. -/
def boundedSortedLists : ℕ → ℕ → List (List ℕ)
  | 0, n => [List.replicate n 0]
  | k + 1, n =>
      (List.range (n + 1)).flatMap fun c =>
        (boundedSortedLists k (n - c)).map fun tail =>
          List.replicate c (k + 1) ++ tail

/-- Boolean test for Havel--Hakimi residue two. -/
def hasResidueTwo (s : List ℕ) : Bool := residueAux s == 2

/-- Boolean test used for the length-fifteen parity certificate. -/
def residueTwoImpliesOddSum (s : List ℕ) : Bool :=
  if hasResidueTwo s then s.sum % 2 == 1 else true

/-- There are `C(22,6)=74613` descending lists of length sixteen bounded by six. -/
theorem length_sixteen_candidate_count :
    (boundedSortedLists 6 16).length = 74613 := by
  decide

/-- None of the bounded descending length-sixteen lists has residue two. -/
theorem no_residue_two_length_sixteen :
    (boundedSortedLists 6 16).all (fun s => !(hasResidueTwo s)) = true := by
  decide

/-- There are `C(21,6)=54264` descending lists of length fifteen bounded by six. -/
theorem length_fifteen_candidate_count :
    (boundedSortedLists 6 15).length = 54264 := by
  decide

/-- Every bounded descending length-fifteen list of residue two has odd sum. -/
theorem residue_two_length_fifteen_has_odd_sum :
    (boundedSortedLists 6 15).all residueTwoImpliesOddSum = true := by
  decide

#print axioms SimpleGraph.C217OrderCertificate.length_sixteen_candidate_count
#print axioms SimpleGraph.C217OrderCertificate.no_residue_two_length_sixteen
#print axioms SimpleGraph.C217OrderCertificate.length_fifteen_candidate_count
#print axioms SimpleGraph.C217OrderCertificate.residue_two_length_fifteen_has_odd_sum

end SimpleGraph.C217OrderCertificate
