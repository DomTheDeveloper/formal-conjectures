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

import FormalConjectures.Paper.ChompStrategyCertificate

/-!
# Three winning opening moves in Chomp

A Chomp position is represented by its row lengths from top to bottom.  A legal bite replaces one
row length by a smaller value and truncates every later row to at most that value.  The move that
eats the poisoned top-left square is excluded.

*References:*
- [All the Winning Bites for a by b Chomp for a and b up to 14 and Two Computational
  Challenges](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/chompc.html)
  by S. B. Ekhad and D. Zeilberger.
- [OEIS A147983](https://oeis.org/A147983)
-/

namespace ChompThreeOpenings

open ChompStrategyCertificate

abbrev Position := List ℕ

/-- A legal Chomp move, expressed by splitting the selected row from its prefix and suffix. -/
def Move (p q : Position) : Prop :=
  ∃ pre w post keep,
    p = pre ++ w :: post ∧
    keep < w ∧
    ¬(pre = [] ∧ keep = 0) ∧
    q = pre ++ keep :: post.map (fun x => min x keep)

private lemma mapped_tail_sum_le (post : List ℕ) (keep : ℕ) :
    (post.map fun x => min x keep).sum ≤ post.sum := by
  induction post with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (min_le_left x keep) ih

/-- Every legal bite strictly decreases the number of remaining squares. -/
theorem move_sum_lt {p q : Position} (h : Move p q) : q.sum < p.sum := by
  rcases h with ⟨pre, w, post, keep, rfl, hkeep, _, rfl⟩
  simp only [List.sum_append, List.sum_cons]
  have htail := mapped_tail_sum_le post keep
  omega

/-- Chomp as a ranked finite game. -/
def game : RankedGame where
  State := Position
  move := Move
  rank := List.sum
  move_rank_lt := move_sum_lt

/-- A rectangular Chomp board. -/
def rectangle (rows columns : ℕ) : Position :=
  List.replicate rows columns

/-- A winning opening is a legal move to a losing position. -/
def WinningOpening (p q : Position) : Prop :=
  Move p q ∧ game.Losing q

/-- Residual position after biting row 5, column 36 in one-based coordinates. -/
def root₁ : Position := [42, 42, 42, 42, 35, 35, 35, 35, 35, 35]

/-- Residual position after biting row 7, column 30 in one-based coordinates. -/
def root₂ : Position := [42, 42, 42, 42, 42, 42, 29, 29, 29, 29]

/-- Residual position after biting row 8, column 26 in one-based coordinates. -/
def root₃ : Position := [42, 42, 42, 42, 42, 42, 42, 25, 25, 25]

theorem root₁_is_move : Move (rectangle 10 42) root₁ := by
  refine ⟨[42, 42, 42, 42], 42, [42, 42, 42, 42, 42], 35, ?_, by omega, by simp, ?_⟩
  · decide
  · decide

theorem root₂_is_move : Move (rectangle 10 42) root₂ := by
  refine ⟨[42, 42, 42, 42, 42, 42], 42, [42, 42, 42], 29, ?_, by omega, by simp, ?_⟩
  · decide
  · decide

theorem root₃_is_move : Move (rectangle 10 42) root₃ := by
  refine ⟨[42, 42, 42, 42, 42, 42, 42], 42, [42, 42], 25, ?_, by omega, by simp, ?_⟩
  · decide
  · decide

/-- Once the three residual positions are certified losing, they give three distinct winning moves. -/
theorem has_three_winning_openings_of_roots
    (h₁ : game.Losing root₁) (h₂ : game.Losing root₂) (h₃ : game.Losing root₃) :
    ∃ q₁ q₂ q₃,
      q₁ ≠ q₂ ∧ q₁ ≠ q₃ ∧ q₂ ≠ q₃ ∧
      WinningOpening (rectangle 10 42) q₁ ∧
      WinningOpening (rectangle 10 42) q₂ ∧
      WinningOpening (rectangle 10 42) q₃ := by
  refine ⟨root₁, root₂, root₃, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · exact ⟨root₁_is_move, h₁⟩
  · exact ⟨root₂_is_move, h₂⟩
  · exact ⟨root₃_is_move, h₃⟩

end ChompThreeOpenings
