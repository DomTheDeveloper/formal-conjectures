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
# Seven-team World Cup polynomial

For `n` labelled teams, a score matrix is an `n × n` matrix of nonnegative integers whose
`(i, j)` entry records the number of goals scored by team `i` against team `j`. Its diagonal is
zero, since a team does not play itself. This file formalises Doron Zeilberger's 2026 challenge to
compute the counting polynomial when there are seven teams and every row and column sum is `r`.

The displayed answer uses the centered variable `x = r + 3` and `y = x²`.

*References:*

- [Doron Zeilberger, *Attendance Quizzes, Solutions, and Some Challenges Related to Dr. Z.'s
  June 30, 2026, DIMACS REU*]
  (https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/DIMACS2026.html)
- [Shalosh B. Ekhad and Doron Zeilberger, *World Cup Enumerative Combinatorics*]
  (https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/worldcup.html)
- [Exact seven-team solution, recurrence, data, and independent regression checks]
  (https://github.com/DomTheDeveloper/ProofPlaygrond/tree/bf698f9a00ffb142966c4b0412528042b6510db5/WorldCup7)
-/

open scoped BigOperators

namespace WorldCup7

/-- A score matrix for `n` labelled teams in which every team scores and concedes exactly `r`
goals. Entries lie in `Fin (r + 1)` because every entry of such a matrix is at most its row sum. -/
def IsScoreMatrix {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) (Fin (r + 1))) : Prop :=
  (∀ i, A i i = 0) ∧
    (∀ i, ∑ j, (A i j : ℕ) = r) ∧
      (∀ j, ∑ i, (A i j : ℕ) = r)

/-- The number of `n × n` score matrices with zero diagonal and every row and column sum equal to
`r`. -/
def scoreMatrixCount (n r : ℕ) : ℕ :=
  ((Finset.univ : Finset (Matrix (Fin n) (Fin n) (Fin (r + 1)))).filter
    fun A ↦ IsScoreMatrix A).card

/-- The proposed degree-29 counting polynomial for the seven-team problem. -/
def solutionPolynomial (r : ℚ) : ℚ :=
  let x := r + 3
  let y := x ^ 2
  x * (x ^ 2 - 1) * (x ^ 2 - 4) *
      (606027774191831 * y ^ 12 - 3685861337229214 * y ^ 11 +
        37765555858458113 * y ^ 10 + 45058773949238216 * y ^ 9 +
        1570392939902887193 * y ^ 8 + 8739034660779266186 * y ^ 7 +
        95377188765692157983 * y ^ 6 + 844891531636894661036 * y ^ 5 +
        6155573446929541440848 * y ^ 4 + 46788350432653174464576 * y ^ 3 +
        271550071954942194604032 * y ^ 2 + 1338033873961407109939200 * y +
        3154971657218398617600000) /
    63155442812426442532454400000

/-- The seven-team World Cup counting function is given by `solutionPolynomial`. -/
@[category research solved, AMS 5 52]
theorem seven_team_world_cup_polynomial (r : ℕ) :
    (scoreMatrixCount 7 r : ℚ) = solutionPolynomial r := by
  sorry

/-- The proposed polynomial has the correct constant term. -/
@[category test, AMS 5 52]
theorem solutionPolynomial_zero : solutionPolynomial 0 = 1 := by
  norm_num [solutionPolynomial]

/-- The proposed polynomial gives `1854` at line sum one, the derangement number `!7`. -/
@[category test, AMS 5 52]
theorem solutionPolynomial_one : solutionPolynomial 1 = 1854 := by
  norm_num [solutionPolynomial]

end WorldCup7
