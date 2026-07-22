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
and $J_{n,n+1}(x) = 0$.

In the classical case $\alpha = 1$, these operators reduce to the usual Bernstein operators.
For $f$ which are $C^2$ on $[0,1]$, one has the classical Voronovskaja
asymptotic formula
\[
\lim_{n \to \infty} n\bigl( B_{n,1} f(x) - f(x) \bigr)
    = \tfrac{1}{2} x(1-x) f''(x).
\]

For $\alpha \neq 1$, the problem is resolved by the first-order formula
\[
\sqrt n\,\bigl(B_{n,\alpha}f(x)-f(x)\bigr)
\longrightarrow
\mu_\alpha\sqrt{x(1-x)}\,f'(x),
\]
where
\[
\mu_\alpha=\int_0^\infty
\left((1-\Phi(t))^\alpha+\Phi(t)^\alpha-1\right)\,dt
\]
and $\Phi$ is the standard Gaussian distribution function.

*References:*

* [Voronovskaja-type Formula for the Bézier Variant of the Bernstein Operators](https://www.math.bas.bg/mathmod/Proceedings_CTF/CTF-2010/files_CTF-2010/Open_problems.pdf),
  by *Ulrich Abel*, in *Constructive Theory of Functions, Sozopol 2010*.
-/
open Topology Filter MeasureTheory ProbabilityTheory Real unitInterval Polynomial
namespace VoronovskajaTypeFormula

/--
Cumulative sum $J_{n,k}(x) = \sum_{j=k}^n p_{n,j}(x)$.
-/
noncomputable def bernsteinTail (n k : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.Icc k n, bernsteinPolynomial ℝ n j

/--
Bézier–type Bernstein operator:
\[
(B_{n,\alpha} f)(x)
= \sum_{k=0}^{n}
f\!\left(\frac{k}{n}\right)
\left(
J_{n,k}(x)^{\alpha}
- J_{n,k+1}(x)^{\alpha}
\right)
\]
-/
noncomputable def bezierBernstein (n : ℕ) (α : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    f (k / n) * ((bernsteinTail n k).eval x ^ α - (bernsteinTail n (k + 1)).eval x ^ α)

/-- The first-order bias constant for the Bézier--Bernstein operator. -/
noncomputable def bezierBias (α : ℝ) : ℝ :=
  ∫ t in Set.Ioi 0,
    (1 - cdf (gaussianReal 0 1) t) ^ α + cdf (gaussianReal 0 1) t ^ α - 1

/--
Classical Voronovskaja theorem (α = 1).

For functions $f$ that are $C^2$ on $[0,1]$, the limit:
\[
n\bigl( B_n f(x) - f(x) \bigr)
\;\longrightarrow\;
\frac{1}{2}\, x(1 - x)\, f''(x)
\]
-/
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
Voronovskaja formula for Bézier--Bernstein operators with shape parameter
$\alpha > 0$, $\alpha \neq 1$.

## Provenance

Solved by Dominic Dabish.

ProofOrchestrator, using OpenAI GPT-5.6 Thinking, assisted with the mathematical
argument and Lean formalization; all formal claims were checked by the pinned
Lean compiler.
-/
@[category research solved, AMS 26 40 47,
  formal_proof using lean4 at "https://github.com/DomTheDeveloper/formal-conjectures/blob/6f53eea73f2198091a7b5822bfdfe4b0d40f21a0/FormalConjectures/Paper/VoronovskajaTypeFormula.lean"]
theorem voronovskaja_theorem.bezier_bernstein_operators
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1)
    (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (hf : ContDiffOn ℝ 2 f I) :
    Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
      (𝓝 answer(bezierBias α * Real.sqrt (x * (1 - x)) *
        iteratedDerivWithin 1 f I x)) := by
  sorry

/-- For every sufficiently large finite smoothness order (in fact every $m \ge 2$), the same
explicit first-order formula holds. -/
@[category research solved, AMS 26 40 47,
  formal_proof using lean4 at "https://github.com/DomTheDeveloper/formal-conjectures/blob/6f53eea73f2198091a7b5822bfdfe4b0d40f21a0/FormalConjectures/Paper/VoronovskajaTypeFormula.lean"]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.eventually_smooth
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    let limitFormula : (ℝ → ℝ) → ℝ → ℝ := answer(fun f x =>
      bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x)
    ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (limitFormula f x)) := by
  sorry

/-- Existence-only consequence of the explicit eventual-smoothness formula. -/
@[category research solved, AMS 26 40 47,
  formal_proof using lean4 at "https://github.com/DomTheDeveloper/formal-conjectures/blob/6f53eea73f2198091a7b5822bfdfe4b0d40f21a0/FormalConjectures/Paper/VoronovskajaTypeFormula.lean"]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.eventually_smooth.limit_exists
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        ∃ L : ℝ,
          Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
            (𝓝 L) := by
  sorry

/-- The smoothness-answer variant is resolved by order two and the same explicit limit formula. -/
@[category research solved, AMS 26 40 47,
  formal_proof using lean4 at "https://github.com/DomTheDeveloper/formal-conjectures/blob/6f53eea73f2198091a7b5822bfdfe4b0d40f21a0/FormalConjectures/Paper/VoronovskajaTypeFormula.lean"]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.answer_smoothness
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    let p : ℕ × ((ℝ → ℝ) → ℝ → ℝ) := answer((2, fun f x =>
      bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))
    let m := p.1
    let limitFormula := p.2
    ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
      Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
        (𝓝 (limitFormula f x)) := by
  sorry

end VoronovskajaTypeFormula
