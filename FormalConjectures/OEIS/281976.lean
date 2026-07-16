/-
Copyright 2025 The Formal Conjectures Authors.

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
# Sum of four squares with square conditions

Any integer $n \geq 0$ can be written as $x^2 + y^2 + z^2 + w^2$ with $x, y, z, w$ nonnegative
integers and $z \leq w$, such that both $x$ and $x + 24y$ are squares.

Zhi-Wei Sun has offered a $2,400 prize for the first proof.

*References:*
- [A281976](https://oeis.org/A281976)
- Z.-W. Sun, "Refining Lagrange's four-square theorem," *J. Number Theory* **175** (2017), 167-190.
  https://doi.org/10.1016/j.jnt.2016.11.008
- Z.-W. Sun, "Restricted sums of four squares," *arXiv:1701.05868* [math.NT], 2017.
  https://arxiv.org/abs/1701.05868
-/

namespace OeisA281976

/-- The predicate that `n` can be written as $x^2 + y^2 + z^2 + w^2$ with $x, y, z, w$ nonnegative
integers, $z \leq w$, such that both $x$ and $x + 24y$ are squares. -/
def IsSumOfFourSquaresWithSquareConditions (n : ℕ) : Prop :=
  ∃ x y z w : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧ z ≤ w ∧ IsSquare x ∧ IsSquare (x + 24 * y)

@[category test, AMS 11]
theorem isSumOfFourSquaresWithSquareConditions_0 : IsSumOfFourSquaresWithSquareConditions 0 :=
  ⟨0, 0, 0, 0, by norm_num⟩

@[category test, AMS 11]
theorem isSumOfFourSquaresWithSquareConditions_8 : IsSumOfFourSquaresWithSquareConditions 8 :=
  ⟨0, 0, 2, 2, by norm_num, by norm_num, ⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩

@[category test, AMS 11]
theorem isSumOfFourSquaresWithSquareConditions_12 : IsSumOfFourSquaresWithSquareConditions 12 :=
  ⟨1, 1, 1, 3, by norm_num, by norm_num, ⟨1, by norm_num⟩, ⟨5, by norm_num⟩⟩

@[category test, AMS 11]
theorem isSumOfFourSquaresWithSquareConditions_23 : IsSumOfFourSquaresWithSquareConditions 23 :=
  ⟨1, 2, 3, 3, by norm_num, by norm_num, ⟨1, by norm_num⟩, ⟨7, by norm_num⟩⟩

@[category test, AMS 11]
theorem isSumOfFourSquaresWithSquareConditions_24 : IsSumOfFourSquaresWithSquareConditions 24 :=
  ⟨4, 0, 2, 2, by norm_num, by norm_num, ⟨2, by norm_num⟩, ⟨2, by norm_num⟩⟩

/-- The first exact parametrized family of admissible `(x,y)` pairs, in the range `r ≤ 6s`. -/
theorem familyOneOfLE (r s z w : ℕ) (hr : r ≤ 6 * s) (hzw : z ≤ w) :
    IsSumOfFourSquaresWithSquareConditions
      ((6 * s - r) ^ 4 + (r * s) ^ 2 + z ^ 2 + w ^ 2) := by
  refine ⟨(6 * s - r) ^ 2, r * s, z, w, ?_, hzw, ?_, ?_⟩
  · ring
  · exact ⟨6 * s - r, by ring⟩
  · refine ⟨6 * s + r, ?_⟩
    have hsub : 6 * s - r + r = 6 * s := Nat.sub_add_cancel hr
    nlinarith

/-- The first exact parametrized family of admissible `(x,y)` pairs, in the range `6s ≤ r`. -/
theorem familyOneOfGE (r s z w : ℕ) (hr : 6 * s ≤ r) (hzw : z ≤ w) :
    IsSumOfFourSquaresWithSquareConditions
      ((r - 6 * s) ^ 4 + (r * s) ^ 2 + z ^ 2 + w ^ 2) := by
  refine ⟨(r - 6 * s) ^ 2, r * s, z, w, ?_, hzw, ?_, ?_⟩
  · ring
  · exact ⟨r - 6 * s, by ring⟩
  · refine ⟨r + 6 * s, ?_⟩
    have hsub : r - 6 * s + 6 * s = r := Nat.sub_add_cancel hr
    nlinarith

/-- The second exact parametrized family of admissible `(x,y)` pairs, in the range `2r ≤ 3s`. -/
theorem familyTwoOfLE (r s z w : ℕ) (hr : 2 * r ≤ 3 * s) (hzw : z ≤ w) :
    IsSumOfFourSquaresWithSquareConditions
      ((3 * s - 2 * r) ^ 4 + (r * s) ^ 2 + z ^ 2 + w ^ 2) := by
  refine ⟨(3 * s - 2 * r) ^ 2, r * s, z, w, ?_, hzw, ?_, ?_⟩
  · ring
  · exact ⟨3 * s - 2 * r, by ring⟩
  · refine ⟨3 * s + 2 * r, ?_⟩
    have hsub : 3 * s - 2 * r + 2 * r = 3 * s := Nat.sub_add_cancel hr
    nlinarith

/-- The second exact parametrized family of admissible `(x,y)` pairs, in the range `3s ≤ 2r`. -/
theorem familyTwoOfGE (r s z w : ℕ) (hr : 3 * s ≤ 2 * r) (hzw : z ≤ w) :
    IsSumOfFourSquaresWithSquareConditions
      ((2 * r - 3 * s) ^ 4 + (r * s) ^ 2 + z ^ 2 + w ^ 2) := by
  refine ⟨(2 * r - 3 * s) ^ 2, r * s, z, w, ?_, hzw, ?_, ?_⟩
  · ring
  · exact ⟨2 * r - 3 * s, by ring⟩
  · refine ⟨2 * r + 3 * s, ?_⟩
    have hsub : 2 * r - 3 * s + 3 * s = 2 * r := Nat.sub_add_cancel hr
    nlinarith

/-- Every admissible representation scales to one of sixteen times the represented integer. -/
theorem mulSixteen {n : ℕ} (h : IsSumOfFourSquaresWithSquareConditions n) :
    IsSumOfFourSquaresWithSquareConditions (16 * n) := by
  rcases h with ⟨x, y, z, w, hn, hzw, hx, hxy⟩
  refine ⟨4 * x, 4 * y, 4 * z, 4 * w, ?_, by omega, ?_, ?_⟩
  · rw [hn]
    ring
  · rcases hx with ⟨a, ha⟩
    refine ⟨2 * a, ?_⟩
    rw [ha]
    ring
  · rcases hxy with ⟨b, hb⟩
    refine ⟨2 * b, ?_⟩
    rw [show 4 * x + 24 * (4 * y) = 4 * (x + 24 * y) by ring, hb]
    ring

/--
**Zhi-Wei Sun's Conjecture (A281976)**: Any integer $n \geq 0$ can be written as $x^2 + y^2 + z^2 + w^2$
with $x, y, z, w$ nonnegative integers and $z \leq w$, such that both $x$ and $x + 24y$ are squares.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) : IsSumOfFourSquaresWithSquareConditions n := by
  sorry

end OeisA281976
