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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.CastBridges

/-!
# Finite-sum factorial reduction for the five-dimensional Geode

The termwise factorial identity is lifted over all four finite summation
indices. This is the exact rational alternating sum appearing before the beta
integral and coefficient extraction in the supplied proof certificate.
-/

namespace Arxiv.«2508.10245».Geode5Proof

open scoped BigOperators

/-- The fully reduced four-dimensional rational sum. -/
def qReducedGeode (n : ℕ) : ℚ :=
  ∑ a ∈ Finset.range (n + 1),
    ∑ b ∈ Finset.range (n + 1),
      ∑ c ∈ Finset.range (n + 1),
        ∑ d ∈ Finset.range (n + 1),
          qReducedSummand n a b c d

/-- The rational benchmark sum equals its collected-factorial form. -/
theorem qGeode5Diagonal_eq_qReducedGeode (n : ℕ) :
    qGeode5Diagonal n = qReducedGeode n := by
  unfold qGeode5Diagonal qReducedGeode
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  change qAlternatingSummand n a b c d = qReducedSummand n a b c d
  apply qAlternatingSummand_eq_qReducedSummand
  all_goals omega

/-- The original integer benchmark casts to the reduced rational sum. -/
theorem cast_geode5Diagonal_eq_qReducedGeode (n : ℕ) :
    (geode5Diagonal n : ℚ) = qReducedGeode n := by
  rw [cast_geode5Diagonal_eq_qGeode5Diagonal,
    qGeode5Diagonal_eq_qReducedGeode]

#print axioms qGeode5Diagonal_eq_qReducedGeode
#print axioms cast_geode5Diagonal_eq_qReducedGeode

end Arxiv.«2508.10245».Geode5Proof
