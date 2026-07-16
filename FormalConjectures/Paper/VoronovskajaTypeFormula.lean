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

import FormalConjectures.Paper.VoronovskajaMain

/-!
# Voronovskaja-type Formula for the Bezier Variant of the Bernstein Operators

The Bézier-type Bernstein operators $B_{n,\alpha}$ for $\alpha > 0$ are defined for
$f : [0,1] \to \mathbb{R}$ by
\[
(B_{n,\alpha} f)(x)
  = \sum_{k=0}^n f\!\left(\frac{k}{n}\right)
    \left( J_{n,k}(x)^{\alpha} - J_{n,k+1}(x)^{\alpha} \right),
\]
where
\[
J_{n,k}(x) = \sum_{j=k}^n p_{n,j}(x),
\qquad
p_{n,j}(x) = \binom{n}{j} x^j(1-x)^{n-j},
\]
and $J_{n,n+1}(x)=0$.

For $\alpha \ne 1$, the `sqrt n` asymptotic is controlled by the mean of the powered-survival
transform of the standard Gaussian law.
-/

open Topology Filter Real unitInterval Polynomial
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval

namespace VoronovskajaTypeFormula

/-- Classical Voronovskaja theorem (`α = 1`). -/
@[category research solved, AMS 26 40 47]
theorem voronovskaja_theorem.bernstein_operators
    (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (hf : ContDiffOn ℝ 2 f I) :
    let f'' : ℝ := iteratedDerivWithin 2 f I x
    Tendsto (fun (n : ℕ) => (n : ℝ) * (bezierBernstein n 1 f x - f x))
    atTop
    (𝓝 ((1 / 2) * x * (1 - x) * f'')) := by
  sorry

/--
Voronovskaja formula for Bézier--Bernstein operators with positive shape parameter.

The constant is
`∫ t in Ioi 0, (1 - Φ t)^α + (Φ t)^α - 1`, where `Φ` is the standard Gaussian CDF.
-/
@[category research open, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1)
    (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (hf : ContDiffOn ℝ 2 f I) :
    Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
      (𝓝 (bezierVoronovskajaConstant α * Real.sqrt (x * (1 - x)) *
        iteratedDerivWithin 1 f I x)) := by
  simpa using tendsto_bezierBernstein_all α hα_pos f hf x hx

/-- Eventual-smoothness variant, with the explicit threshold `m = 2`. -/
@[category research open, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.eventually_smooth
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    let limitFormula : (ℝ → ℝ) → ℝ → ℝ := fun f x ↦
      bezierVoronovskajaConstant α * Real.sqrt (x * (1 - x)) *
        iteratedDerivWithin 1 f I x
    ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (limitFormula f x)) := by
  dsimp only
  refine eventually_atTop.2 ⟨2, fun m hm f x hx hfm ↦ ?_⟩
  apply tendsto_bezierBernstein_all α hα_pos f _ x hx
  exact hfm.of_le (by exact_mod_cast hm)

/-- Existence-only consequence of the explicit formula. -/
@[category research open, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.eventually_smooth.limit_exists
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        ∃ L : ℝ,
          Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
            (𝓝 L) := by
  refine eventually_atTop.2 ⟨2, fun m hm f x hx hfm ↦ ?_⟩
  refine ⟨bezierVoronovskajaConstant α * Real.sqrt (x * (1 - x)) *
    iteratedDerivWithin 1 f I x, ?_⟩
  apply tendsto_bezierBernstein_all α hα_pos f _ x hx
  exact hfm.of_le (by exact_mod_cast hm)

/-- Concrete answer to the smoothness-threshold variant: order two and the explicit formula above. -/
@[category research open, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.answer_smoothness
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    let p : ℕ × ((ℝ → ℝ) → ℝ → ℝ) :=
      (2, fun f x ↦ bezierVoronovskajaConstant α * Real.sqrt (x * (1 - x)) *
        iteratedDerivWithin 1 f I x)
    let m := p.1
    let limitFormula := p.2
    ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
      Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
        (𝓝 (limitFormula f x)) := by
  dsimp only
  intro f x hx hf
  exact tendsto_bezierBernstein_all α hα_pos f hf x hx

end VoronovskajaTypeFormula
