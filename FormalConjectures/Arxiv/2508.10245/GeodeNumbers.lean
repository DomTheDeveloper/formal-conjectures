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
# The challenge of computing five-dimensional Geode numbers

*References:*
- [The Challenge of Computing Geode Numbers](https://arxiv.org/abs/2508.10245),
  by Tewodros Amdeberhan, Manuel Kauers, and Doron Zeilberger
- [Lattice Paths and the Geode](https://arxiv.org/abs/2507.09405), by Ira Gessel

The cited challenge asks for the exact value of
$G(1000,1000,1000,1000,1000)$ and offers a donation to the OEIS for its
correct determination. We use the finite alternating-sum coefficient formula
obtained by expanding the inverse of $t_1+\cdots+t_5$ in the $t_1$ direction.
-/

namespace Arxiv.«2508.10245»

open scoped BigOperators

/-- The five-variable hyper-Catalan number
$$
C(m_1,\ldots,m_5)=
\frac{(2m_1+3m_2+4m_3+5m_4+6m_5)!}
{(1+m_1+2m_2+3m_3+4m_4+5m_5)!m_1!m_2!m_3!m_4!m_5!}.
$$
-/
def hyperCatalan5 (m₁ m₂ m₃ m₄ m₅ : ℕ) : ℕ :=
  Nat.factorial (2 * m₁ + 3 * m₂ + 4 * m₃ + 5 * m₄ + 6 * m₅) /
    (Nat.factorial (1 + m₁ + 2 * m₂ + 3 * m₃ + 4 * m₄ + 5 * m₅) *
      Nat.factorial m₁ * Nat.factorial m₂ * Nat.factorial m₃ *
      Nat.factorial m₄ * Nat.factorial m₅)

/-- The multinomial coefficient $\binom{a+b+c+d}{a,b,c,d}$. -/
def multinomial4 (a b c d : ℕ) : ℕ :=
  Nat.factorial (a + b + c + d) /
    (Nat.factorial a * Nat.factorial b * Nat.factorial c * Nat.factorial d)

/--
The diagonal five-dimensional Geode number, expressed by the finite coefficient identity
$$
G(n,n,n,n,n)=\sum_{j_2,j_3,j_4,j_5=0}^{n}(-1)^r
\binom{r}{j_2,j_3,j_4,j_5}
C(n+1+r,n-j_2,n-j_3,n-j_4,n-j_5),
$$
where $r=j_2+j_3+j_4+j_5$.
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

/--
Determine the exact value of the five-dimensional diagonal Geode number
$G(1000,1000,1000,1000,1000)$.
-/
@[category research open, AMS 5]
theorem geode5_1000 : geode5Diagonal 1000 = answer(sorry) := by
  sorry

end Arxiv.«2508.10245»
