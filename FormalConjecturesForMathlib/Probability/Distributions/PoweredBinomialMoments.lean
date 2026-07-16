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

public import FormalConjecturesForMathlib.Probability.Distributions.PoweredBinomialLimit

/-!
# Truncated moments of powered binomial laws

Weak convergence alone does not control the unbounded identity function.  It does immediately
control every clipped identity.  This file records that rigorous intermediate result; removing the
clip is precisely the remaining uniform-integrability step in the first-moment argument.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology unitInterval BoundedContinuousFunction

namespace ProbabilityTheory

/-- The identity on `[-R,R]`, clipped to stay in that interval outside it. -/
@[expose]
noncomputable def clippedIdentity (R : ℝ) (hR : 0 ≤ R) : ℝ →ᵇ ℝ where
  toFun z := max (-R) (min z R)
  continuous_toFun := continuous_const.max (continuous_id.min continuous_const)
  map_bounded' := by
    refine ⟨2 * R, fun x y ↦ ?_⟩
    rw [Real.dist_eq, abs_le]
    have hxlo : -R ≤ max (-R) (min x R) := le_max_left _ _
    have hylo : -R ≤ max (-R) (min y R) := le_max_left _ _
    have hxhi : max (-R) (min x R) ≤ R := by
      exact max_le (by linarith) (min_le_right _ _)
    have hyhi : max (-R) (min y R) ≤ R := by
      exact max_le (by linarith) (min_le_right _ _)
    constructor <;> linarith

@[simp]
lemma clippedIdentity_apply (R : ℝ) (hR : 0 ≤ R) (z : ℝ) :
    clippedIdentity R hR z = max (-R) (min z R) := rfl

lemma clippedIdentity_eq_self {R z : ℝ} (hR : 0 ≤ R) (hz : z ∈ Icc (-R) R) :
    clippedIdentity R hR z = z := by
  simp [clippedIdentity, hz.1, hz.2]

lemma abs_clippedIdentity_le (R : ℝ) (hR : 0 ≤ R) (z : ℝ) :
    |clippedIdentity R hR z| ≤ R := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

/-- Every fixed clipped first moment of the powered standardized binomial law converges to the
corresponding clipped moment of the powered Gaussian law. -/
lemma tendsto_integral_clippedIdentity_poweredStandardizedBinomial
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (α : ℝ) (hα : 0 < α) (R : ℝ) (hR : 0 ≤ R) :
    Tendsto
      (fun n ↦ ∫ z, clippedIdentity R hR z
        ∂(poweredStandardizedBinomialProbability n p α hα : Measure ℝ))
      atTop
      (𝓝 (∫ z, clippedIdentity R hR z
        ∂(poweredGaussianProbability α hα : Measure ℝ))) := by
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_poweredStandardizedBinomialProbability p hp0 hp1 α hα))
    (clippedIdentity R hR)

end ProbabilityTheory
