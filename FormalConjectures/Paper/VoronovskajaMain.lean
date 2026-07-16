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

public import FormalConjectures.Paper.VoronovskajaRemainder
public import FormalConjectures.Paper.VoronovskajaEndpoints

/-!
# The Bézier--Bernstein Voronovskaja formula

The first centered moment converges to the powered-Gaussian constant and the quadratic Taylor
remainder is negligible at the `sqrt n` scale.  The endpoints are exact reproduction cases.
-/

public section

noncomputable section

open Topology Filter Real unitInterval Polynomial
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval

namespace VoronovskajaTypeFormula

/-- The explicit constant in the Bézier--Bernstein Voronovskaja formula. -/
@[expose]
noncomputable def bezierVoronovskajaConstant (α : ℝ) : ℝ :=
  poweredGaussianFirstMomentConstant α

lemma bezierVoronovskajaConstant_eq_integral (α : ℝ) :
    bezierVoronovskajaConstant α =
      ∫ t in Ioi 0,
        (1 - cdf (gaussianReal 0 1) t) ^ α +
          cdf (gaussianReal 0 1) t ^ α - 1 := rfl

/-- Interior form of the exact asymptotic. -/
lemma tendsto_bezierBernstein_interior
    (α : ℝ) (hα : 0 < α)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I)
    (x : I) (hx0 : 0 < (x : ℝ)) (hx1 : (x : ℝ) < 1) :
    Tendsto
      (fun n : ℕ ↦ Real.sqrt n *
        (bezierBernstein n α f (x : ℝ) - f (x : ℝ)))
      atTop
      (𝓝 (bezierVoronovskajaConstant α *
        Real.sqrt ((x : ℝ) * (1 - (x : ℝ))) *
          iteratedDerivWithin 1 f I (x : ℝ))) := by
  let slope : ℝ := iteratedDerivWithin 1 f I (x : ℝ)
  have hmoment := tendsto_sqrt_mul_bezierCenteredMoment x hx0 hx1 α hα
  have hlinear : Tendsto
      (fun n : ℕ ↦ slope * (Real.sqrt n * bezierCenteredMoment n α (x : ℝ)))
      atTop
      (𝓝 (slope *
        (bernoulliStdDev x * poweredGaussianFirstMomentConstant α))) :=
    tendsto_const_nhds.mul hmoment
  have hrem := tendsto_sqrt_mul_bezierTaylorRemainder α hα f hf x hx0 hx1
  have hsum := hlinear.add hrem
  refine hsum.congr' ?_
  filter_upwards with n
  rw [bezierBernstein_sub_eq_moment_add_remainder n hα f (x : ℝ) slope]
  change Real.sqrt n *
      (slope * bezierCenteredMoment n α (x : ℝ) +
        bezierTaylorRemainder n α f (x : ℝ) slope) = _
  ring
  all_goals
    simp only [slope, bezierVoronovskajaConstant, bernoulliStdDev]
    ring

/-- Exact Bézier--Bernstein Voronovskaja formula on the whole unit interval. -/
lemma tendsto_bezierBernstein_all
    (α : ℝ) (hα : 0 < α)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f I)
    (x : ℝ) (hx : x ∈ I) :
    Tendsto
      (fun n : ℕ ↦ Real.sqrt n * (bezierBernstein n α f x - f x))
      atTop
      (𝓝 (bezierVoronovskajaConstant α * Real.sqrt (x * (1 - x)) *
        iteratedDerivWithin 1 f I x)) := by
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · simpa using tendsto_bezierBernstein_zero hα f
  rcases eq_or_lt_of_le hx.2 with hx1eq | hx1
  · subst x
    simpa using tendsto_bezierBernstein_one hα f
  · let xI : I := ⟨x, hx⟩
    simpa [xI] using tendsto_bezierBernstein_interior α hα f hf xI hx0 hx1

end VoronovskajaTypeFormula
