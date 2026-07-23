/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.OEIS.A147983.KernelCertificate

/-!
# The 10 × 42 Chomp three-opening statement

A position is a nonincreasing list of row lengths.  The poisoned square is the first square of the
first row, so a first-row move must leave a positive row length.  P-positions are represented by
actual finite normal-play losing proofs rather than by an external classification predicate.
-/

namespace OeisA147983

/-- Cut every row in a suffix to length at most `t`. -/
def cutSuffix (t : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => min x t :: cutSuffix t xs

/-- The Chomp position obtained by biting row `i` and leaving `t` squares in that row. -/
def bite : ℕ → ℕ → List ℕ → List ℕ
  | _, _, [] => []
  | 0, t, x :: xs => cutSuffix t (x :: xs)
  | i + 1, t, x :: xs => x :: bite i t xs

/-- `q` is obtainable from `p` by one legal Chomp move. -/
def Move (p q : List ℕ) : Prop :=
  ∃ i t : ℕ,
    i < p.length ∧
      t < p.getD i 0 ∧
      (i = 0 → 0 < t) ∧
      q = bite i t p

/-- A Chomp P-position has a kernel-checked losing outcome proof. -/
def IsPPosition (p : List ℕ) : Prop :=
  KernelCertificate.IsLosing Move p

/-- A winning opening is a legal move to a P-position. -/
def IsWinningOpening (rectangle child : List ℕ) : Prop :=
  Move rectangle child ∧ IsPPosition child

/-- The initial `10 × 42` rectangle. -/
def rectangle : List ℕ := [42, 42, 42, 42, 42, 42, 42, 42, 42, 42]

/-- The child left by biting row 5 at column 36. -/
def child₁ : List ℕ := [42, 42, 42, 42, 35, 35, 35, 35, 35, 35]

/-- The child left by biting row 7 at column 30. -/
def child₂ : List ℕ := [42, 42, 42, 42, 42, 42, 29, 29, 29, 29]

/-- The child left by biting row 8 at column 26. -/
def child₃ : List ℕ := [42, 42, 42, 42, 42, 42, 42, 25, 25, 25]

/-- The first displayed child is reached by the claimed legal opening move. -/
theorem child₁_is_legal_move : Move rectangle child₁ := by
  refine ⟨4, 35, by decide, by decide, by simp, ?_⟩
  rfl

/-- The second displayed child is reached by the claimed legal opening move. -/
theorem child₂_is_legal_move : Move rectangle child₂ := by
  refine ⟨6, 29, by decide, by decide, by simp, ?_⟩
  rfl

/-- The third displayed child is reached by the claimed legal opening move. -/
theorem child₃_is_legal_move : Move rectangle child₃ := by
  refine ⟨7, 25, by decide, by decide, by simp, ?_⟩
  rfl

/-- The three candidate children are pairwise distinct. -/
theorem candidate_children_pairwise_distinct :
    child₁ ≠ child₂ ∧ child₁ ≠ child₃ ∧ child₂ ≠ child₃ := by
  decide

/-- Three kernel-checked losing proofs imply the exact three-opening challenge statement. -/
theorem three_openings_of_losing
    (h₁ : IsPPosition child₁) (h₂ : IsPPosition child₂) (h₃ : IsPPosition child₃) :
    IsWinningOpening rectangle child₁ ∧
      IsWinningOpening rectangle child₂ ∧
      IsWinningOpening rectangle child₃ ∧
      child₁ ≠ child₂ ∧ child₁ ≠ child₃ ∧ child₂ ≠ child₃ := by
  rcases candidate_children_pairwise_distinct with ⟨h₁₂, h₁₃, h₂₃⟩
  exact ⟨⟨child₁_is_legal_move, h₁⟩, ⟨child₂_is_legal_move, h₂⟩,
    ⟨child₃_is_legal_move, h₃⟩, h₁₂, h₁₃, h₂₃⟩

end OeisA147983
