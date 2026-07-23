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
# Monochromatic checkerboard no-three-in-line bound

On the `n × n` integer grid, color a point `(i,j)` by the parity of `i+j`.
The theorem below states that, for every `n ≥ 6`, a no-three-collinear subset
of either checkerboard color class contains at most `2n-4` points.

The collinearity condition is Euclidean: it is expressed by the vanishing of
the integer determinant and therefore includes lines of every slope.
-/

namespace MonochromaticCheckerboardNoThreeInLine

/-- A point of the `n × n` integer grid. -/
abbrev Point (n : ℕ) := Fin n × Fin n

/-- Twice the signed Euclidean area of the triangle `a b c`. -/
def determinant {n : ℕ} (a b c : Point n) : ℤ :=
  ((b.1.1 : ℤ) - (a.1.1 : ℤ)) * ((c.2.1 : ℤ) - (a.2.1 : ℤ)) -
    ((b.2.1 : ℤ) - (a.2.1 : ℤ)) * ((c.1.1 : ℤ) - (a.1.1 : ℤ))

/-- Membership in one of the two checkerboard color classes. -/
def InColor {n : ℕ} (parity : ℕ) (p : Point n) : Prop :=
  (p.1.1 + p.2.1) % 2 = parity % 2

/-- Every selected point lies in the specified checkerboard color class. -/
def Monochromatic {n : ℕ} (parity : ℕ) (s : Finset (Point n)) : Prop :=
  ∀ p : ↥s, InColor parity p.1

/-- No three distinct selected points are Euclidean-collinear. -/
def NoThreeInLine {n : ℕ} (s : Finset (Point n)) : Prop :=
  ∀ a b c : ↥s, a ≠ b → a ≠ c → b ≠ c →
    determinant a.1 b.1 c.1 ≠ 0

/--
For every `n ≥ 6`, every no-three-in-line subset of either monochromatic
checkerboard color class has cardinality at most `2n-4`.

The proof combines exact `6 × 6` certificates, a small exceptional `7 × 7`
line-cover certificate, and uniform nonnegative quadratic weighted-line
certificates for all larger odd and even boards.

Solved by Dominic Dabish.

ProofOrchestrator, using OpenAI GPT-5.6 Thinking, assisted with the mathematical
argument and Lean formalization; all formal claims were checked by the pinned
Lean compiler.
-/
@[category research solved, AMS 5 52,
  formal_proof using lean4 at
    "https://github.com/DomTheDeveloper/crl/blob/27a800672db58c9fe0c3d02b48c798347fb02fd5/proofs/lean/Checkerboard/Checkerboard/AllNTheorem.lean"]
theorem checkerboard_upper_all_n {n parity : ℕ}
    (hn : 6 ≤ n) (hp : parity = 0 ∨ parity = 1)
    (s : Finset (Point n))
    (hcolor : Monochromatic parity s) (hntil : NoThreeInLine s) :
    s.card ≤ 2 * n - 4 := by
  sorry

end MonochromaticCheckerboardNoThreeInLine
