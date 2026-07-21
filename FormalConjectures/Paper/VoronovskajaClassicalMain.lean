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
module

public import FormalConjectures.Paper.VoronovskajaClassicalRemainder
public import FormalConjectures.Paper.VoronovskajaEndpoints

/-!
# Classical Bernstein Voronovskaja theorem

The first centered moment vanishes exactly and the second centered moment is `x(1-x)/n`.  The
remaining second-order Taylor error is negligible after multiplication by `n`.
-/

public section

noncomputable section

open Topology Filter Real unitInterval Polynomial
open Set

namespace VoronovskajaTypeFormula

private lemma bezierTaylorRemainder_one_eq_second
    (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    bezierTaylorRemainder n 1 f x (iteratedDerivWithin 1 f I x) =
      (1 / 2 : ℝ) * iteratedDerivWithin 2 f I x *
        (∑ k ∈ Finset.range (n + 1),
          ((((k : ℝ) / (n : ℝ)) - x) ^ 2) * bezierWeight n k 1 x) +
      classicalSecondRemainderSum n f x := by
  rw [bezierTaylorRemainder, classicalSecondRemainderSum]
  rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [classicalSecondRemainder]
  ring

/-- Exact classical error decomposition for positive `n`. -/
lemma nat_mul_bezierBernstein_one_sub_eq
    (n : ℕ) (hn : 0 < n)
    (f : ℝ → ℝ) (x : I) :
    (n : ℝ) * (bezierBernstein n 1 f (x : ℝ) - f (x : ℝ)) =
      (1 / 2 : ℝ) * (x : ℝ) * (1 - (x : ℝ)) *
        iteratedDerivWithin 2 f I (x : ℝ) +
      (n : ℝ) * classicalSecondRemainderSum n f (x : ℝ) := by
  rw [bezierBernstein_sub_eq_moment_add_remainder n one_pos f (x : ℝ)
    (iteratedDerivWithin 1 f I (x : ℝ))]
  rw [bezierCenteredMoment_one_eq_zero n hn, mul_zero, zero_add]
  rw [bezierTaylorRemainder_one_eq_second]
  rw [sum_sq_centered_bezierWeight_one n hn x]
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']

/-- Classical Voronovskaja formula at an interior point. -/
lemma tendsto_classical_bezierBernstein_interior
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I)
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) *
        (bezierBernstein n 1 f (x : ℝ) - f (x : ℝ)))
      atTop
      (𝓝 ((1 / 2 : ℝ) * (x : ℝ) * (1 - (x : ℝ)) *
        iteratedDerivWithin 2 f I (x : ℝ))) := by
  have hrem := tendsto_nat_mul_classicalSecondRemainderSum f hf x hx0 hx1
  have hsum : Tendsto
      (fun n : ℕ ↦
        (1 / 2 : ℝ) * (x : ℝ) * (1 - (x : ℝ)) *
            iteratedDerivWithin 2 f I (x : ℝ) +
          (n : ℝ) * classicalSecondRemainderSum n f (x : ℝ))
      atTop
      (𝓝 ((1 / 2 : ℝ) * (x : ℝ) * (1 - (x : ℝ)) *
        iteratedDerivWithin 2 f I (x : ℝ))) := by
    simpa using tendsto_const_nhds.add hrem
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩
  refine hsum.congr' ?_
  filter_upwards [hnpos] with n hn
  exact (nat_mul_bezierBernstein_one_sub_eq n hn f x).symm

/-- Classical Voronovskaja formula on the whole unit interval. -/
lemma tendsto_classical_bezierBernstein_all
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I)
    (x : ℝ) (hx : x ∈ I) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) * (bezierBernstein n 1 f x - f x))
      atTop
      (𝓝 ((1 / 2 : ℝ) * x * (1 - x) * iteratedDerivWithin 2 f I x)) := by
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · simp [bezierBernstein_zero _ one_pos f]
  rcases eq_or_lt_of_le hx.2 with hx1eq | hx1
  · subst x
    apply tendsto_atTop_of_eventually_const (i₀ := 1)
    intro n hn
    have hnpos : 0 < n := by omega
    simp [bezierBernstein_one n hnpos one_pos f]
  · let xI : I := ⟨x, hx⟩
    simpa [xI] using tendsto_classical_bezierBernstein_interior f hf xI hx0 hx1

end VoronovskajaTypeFormula
