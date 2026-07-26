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

import FormalConjectures.OEIS.«280831»

/-!
# Parametric families for Sun's 1680-conjecture

This file records two concrete reductions toward OEIS A280831.

First, every three-square representation is automatically admissible by taking
`z = 0`. Thus only the classical Legendre exceptional shape needs additional
work.

Second, whenever `c^4 + 1680 d = q^2`, choosing

`x = c y`, `z = d y`

makes the quartic condition a square identically. This yields an explicit
family of admissible integers

`(c^2 + 1 + d^2) y^2 + w^2`.
-/

namespace OeisA280831

/-- Every representation by three squares gives an A280831 representation by taking `z = 0`. -/
theorem of_three_squares (n x y w : ℕ) (h : n = x ^ 2 + y ^ 2 + w ^ 2) : A n := by
  refine ⟨x, y, 0, w, ?_, ?_⟩
  · simpa [h, add_assoc]
  · refine ⟨x ^ 2, ?_⟩
    ring

/-- General algebraic family: a solution of `c^4 + 1680 d = q^2` gives infinitely many
A280831 representations. -/
theorem parametric_family (c d q y w : ℕ) (h : c ^ 4 + 1680 * d = q ^ 2) :
    A ((c ^ 2 + 1 + d ^ 2) * y ^ 2 + w ^ 2) := by
  refine ⟨c * y, y, d * y, w, ?_, ?_⟩
  · ring
  · refine ⟨q * y ^ 2, ?_⟩
    calc
      (c * y) ^ 4 + 1680 * y ^ 3 * (d * y) =
          (c ^ 4 + 1680 * d) * y ^ 4 := by ring
      _ = q ^ 2 * y ^ 4 := by rw [h]
      _ = (q * y ^ 2) * (q * y ^ 2) := by ring

/-- The identity `1^4 + 1680 = 41^2` gives every number `3 y^2 + w^2`. -/
theorem family_three (y w : ℕ) : A (3 * y ^ 2 + w ^ 2) := by
  simpa using parametric_family 1 1 41 y w (by norm_num)

/-- The identity `1^4 + 1680 · 3 = 71^2` gives every number `11 y^2 + w^2`. -/
theorem family_eleven (y w : ℕ) : A (11 * y ^ 2 + w ^ 2) := by
  simpa using parametric_family 1 3 71 y w (by norm_num)

/-- The identity `4^4 + 1680 = 44^2` gives every number `18 y^2 + w^2`. -/
theorem family_eighteen (y w : ℕ) : A (18 * y ^ 2 + w ^ 2) := by
  simpa using parametric_family 4 1 44 y w (by norm_num)

#print axioms of_three_squares
#print axioms parametric_family
#print axioms family_three
#print axioms family_eleven
#print axioms family_eighteen

end OeisA280831
