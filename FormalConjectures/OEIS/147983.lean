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

import FormalConjectures.Util.ProblemImports

/-!
# A Chomp rectangle with three winning opening moves

A Chomp position is represented by a nonincreasing list of row lengths. The poisoned square
is the leftmost square of the first row. Consequently, a move in the first row must leave at
least one square, while a move in any later row may leave zero squares.

The second computational challenge of Ekhad and Zeilberger asks for a rectangular Chomp board
with at least three winning opening moves. The witness formalized here is the `10 × 42`
rectangle.

*References:*
- [A147983](https://oeis.org/A147983)
- [S. B. Ekhad and D. Zeilberger, *All the Winning Bites for a by b Chomp for a and b up to 14
  and Two Computational Challenges*](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/chompc.html)
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

/-- A list of row lengths is a Ferrers position when it is nonempty and nonincreasing. -/
def IsFerrers : List ℕ → Prop
  | [] => False
  | [_] => True
  | x :: y :: xs => y ≤ x ∧ IsFerrers (y :: xs)

/-- A legal Chomp position contains the poisoned square and has nonincreasing row lengths. -/
def IsPosition (p : List ℕ) : Prop := IsFerrers p ∧ 0 < p.getD 0 0

/-- `q` is obtainable from `p` by one legal Chomp move.

The condition `i = 0 → 0 < t` forbids taking the poisoned square.
-/
def Move (p q : List ℕ) : Prop :=
  ∃ i t : ℕ,
    i < p.length ∧
      t < p.getD i 0 ∧
      (i = 0 → 0 < t) ∧
      q = bite i t p

/-- A set of positions is a complete set of Chomp P-positions when no member can move to
another member and every legal position outside the set can move to a member. -/
def IsPSet (P : Set (List ℕ)) : Prop :=
  (∀ ⦃p⦄, p ∈ P → IsPosition p) ∧
    (∀ ⦃p q⦄, p ∈ P → Move p q → q ∉ P) ∧
    (∀ ⦃p⦄, IsPosition p → p ∉ P → ∃ q ∈ P, Move p q)

/-- A Chomp position is a P-position if it belongs to a complete P-set. -/
def IsPPosition (p : List ℕ) : Prop := ∃ P : Set (List ℕ), IsPSet P ∧ p ∈ P

/-- A winning opening is a legal first move to a P-position. -/
def IsWinningOpening (rectangle child : List ℕ) : Prop :=
  Move rectangle child ∧ IsPPosition child

/--
"Find a and b such that an a by b Chomp has (at least) THREE winning moves."

The `10 × 42` rectangle is a witness. In row/column coordinates counted from one, the moves
are `(5, 36)`, `(7, 30)`, and `(8, 26)`. Equivalently, they leave the three displayed Ferrers
positions.
-/
@[category research solved, AMS 5]
theorem chomp_10_by_42_has_three_winning_openings :
    let rectangle := [42, 42, 42, 42, 42, 42, 42, 42, 42, 42]
    let child₁ := [42, 42, 42, 42, 35, 35, 35, 35, 35, 35]
    let child₂ := [42, 42, 42, 42, 42, 42, 29, 29, 29, 29]
    let child₃ := [42, 42, 42, 42, 42, 42, 42, 25, 25, 25]
    IsWinningOpening rectangle child₁ ∧
      IsWinningOpening rectangle child₂ ∧
      IsWinningOpening rectangle child₃ ∧
      child₁ ≠ child₂ ∧ child₁ ≠ child₃ ∧ child₂ ≠ child₃ := by
  sorry

end OeisA147983
