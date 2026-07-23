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

import FormalConjecturesUtil

/-!
# Three winning opening moves in Chomp

This file gives an exact finite-game specification of rectangular Chomp and isolates the
three concrete losing-position obligations for the proposed `10 × 42` witness.

*Reference:*
- [All the Winning Bites for a by b Chomp for a and b up to 14 and Two Computational
  Challenges](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/chompc.html)
  by S. B. Ekhad and D. Zeilberger.
-/

namespace ChompThreeOpenings

/-- A Ferrers Chomp position, represented by row lengths from top to bottom. -/
abbrev Position := List ℕ

/-- Bite in `row`, leaving `keep` squares in that row and truncating every lower row. -/
def bite (p : Position) (row keep : ℕ) : Position :=
  p.take row ++ (p.drop row).map (fun width => min width keep)

/-- All legal Chomp options. The poisoned top-left square is never offered as a move. -/
def options (p : Position) : List Position :=
  (List.range p.length).flatMap fun row =>
    match p.get? row with
    | none => []
    | some width =>
        (List.range width).filterMap fun keep =>
          if row = 0 ∧ keep = 0 then none else some (bite p row keep)

/-- Bounded normal-play outcome recursion. `true` means the player to move can force a win. -/
def winningWithin : ℕ → Position → Bool
  | 0, _ => false
  | fuel + 1, p => (options p).any fun q => !(winningWithin fuel q)

/-- Chomp outcome, using the number of remaining squares as a valid turn bound. -/
def winning (p : Position) : Bool :=
  winningWithin p.sum p

/-- A previous-player win (losing position for the player to move). -/
def PPosition (p : Position) : Prop :=
  winning p = false

/-- A winning opening is a legal move to a P-position. -/
def WinningOpening (p q : Position) : Prop :=
  q ∈ options p ∧ PPosition q

/-- The position is a rectangle with the specified number of rows and columns. -/
def rectangle (rows columns : ℕ) : Position :=
  List.replicate rows columns

/-- A position has at least three pairwise-distinct winning openings. -/
def HasThreeWinningOpenings (p : Position) : Prop :=
  ∃ q₁ q₂ q₃,
    q₁ ≠ q₂ ∧ q₁ ≠ q₃ ∧ q₂ ≠ q₃ ∧
      WinningOpening p q₁ ∧ WinningOpening p q₂ ∧ WinningOpening p q₃

/-- Residual position after biting row 5, column 36 (one-based coordinates). -/
def root₁ : Position := [42, 42, 42, 42, 35, 35, 35, 35, 35, 35]

/-- Residual position after biting row 7, column 30 (one-based coordinates). -/
def root₂ : Position := [42, 42, 42, 42, 42, 42, 29, 29, 29, 29]

/-- Residual position after biting row 8, column 26 (one-based coordinates). -/
def root₃ : Position := [42, 42, 42, 42, 42, 42, 42, 25, 25, 25]

/-- The three explicit bites are distinct legal options of the `10 × 42` rectangle. -/
@[category test, AMS 5 91]
theorem roots_are_distinct_legal_options :
    root₁ ∈ options (rectangle 10 42) ∧
    root₂ ∈ options (rectangle 10 42) ∧
    root₃ ∈ options (rectangle 10 42) ∧
    root₁ ≠ root₂ ∧ root₁ ≠ root₃ ∧ root₂ ≠ root₃ := by
  decide

/--
The exact remaining proof boundary: once the three displayed residual positions are certified
as P-positions, the `10 × 42` rectangle has at least three winning first moves.
-/
@[category API, AMS 5 91]
theorem has_three_winning_openings_of_roots
    (h₁ : PPosition root₁) (h₂ : PPosition root₂) (h₃ : PPosition root₃) :
    HasThreeWinningOpenings (rectangle 10 42) := by
  rcases roots_are_distinct_legal_options with ⟨hm₁, hm₂, hm₃, hne₁₂, hne₁₃, hne₂₃⟩
  exact ⟨root₁, root₂, root₃, hne₁₂, hne₁₃, hne₂₃,
    ⟨hm₁, h₁⟩, ⟨hm₂, h₂⟩, ⟨hm₃, h₃⟩⟩

end ChompThreeOpenings
