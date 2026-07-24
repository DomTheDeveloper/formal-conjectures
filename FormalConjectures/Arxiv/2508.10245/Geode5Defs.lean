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
# Definitions for the five-dimensional Geode challenge

This small base module contains only the benchmark definitions.  The complete
proof imports it; the public benchmark module can therefore import the proof
without forming an import cycle.
-/

namespace Arxiv.«2508.10245»

open scoped BigOperators

/-- The five-variable hyper-Catalan number. -/
def hyperCatalan5 (m₁ m₂ m₃ m₄ m₅ : ℕ) : ℕ :=
  Nat.factorial (2 * m₁ + 3 * m₂ + 4 * m₃ + 5 * m₄ + 6 * m₅) /
    (Nat.factorial (1 + m₁ + 2 * m₂ + 3 * m₃ + 4 * m₄ + 5 * m₅) *
      Nat.factorial m₁ * Nat.factorial m₂ * Nat.factorial m₃ *
      Nat.factorial m₄ * Nat.factorial m₅)

/-- The multinomial coefficient `binom (a+b+c+d) (a,b,c,d)`. -/
def multinomial4 (a b c d : ℕ) : ℕ :=
  Nat.factorial (a + b + c + d) /
    (Nat.factorial a * Nat.factorial b * Nat.factorial c * Nat.factorial d)

/--
The diagonal five-dimensional Geode number, expressed by the finite
alternating-sum coefficient identity.
-/
def geode5Diagonal (n : ℕ) : ℤ :=
  ∑ j₂ ∈ Finset.range (n + 1),
    ∑ j₃ ∈ Finset.range (n + 1),
      ∑ j₄ ∈ Finset.range (n + 1),
        ∑ j₅ ∈ Finset.range (n + 1),
          (-1 : ℤ) ^ (j₂ + j₃ + j₄ + j₅) *
            (multinomial4 j₂ j₃ j₄ j₅ : ℤ) *
              (hyperCatalan5 (n + 1 + j₂ + j₃ + j₄ + j₅)
                (n - j₂) (n - j₃) (n - j₄) (n - j₅) : ℤ)

end Arxiv.«2508.10245»
