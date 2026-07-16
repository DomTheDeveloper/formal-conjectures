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

public import Mathlib.Probability.Distributions.Gaussian.Real

import FormalConjecturesForMathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import FormalConjecturesForMathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic.Convert

/-!
# Central-limit characteristic-function estimate

Minimal compatibility backport for the mathlib snapshot pinned by formal-conjectures. The full
independent-sum CLT is not needed here; the Bézier--Bernstein proof only uses the standard
characteristic-function power limit for one centered, unit-variance law.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter Asymptotics
open scoped Real Topology

namespace ProbabilityTheory

private lemma tendsto_pow_exp_of_isLittleO_sub_add_div_compat {f : ℕ → ℂ} (t : ℂ)
    (hf : (fun n ↦ f n - (1 + t / n)) =o[atTop] fun n ↦ 1 / (n : ℂ)) :
    Tendsto (fun n ↦ f n ^ n) atTop (𝓝 (exp t)) := by
  rw [show (fun n ↦ f n ^ n) = (fun n ↦ (1 + (f n - 1)) ^ n) by ext; simp]
  refine Complex.tendsto_one_add_pow_exp_of_tendsto (tendsto_sub_nhds_zero_iff.1 ?_)
  convert hf.tendsto_inv_smul_nhds_zero.congr' ?_ using 2
  filter_upwards [eventually_ne_atTop 0] with n h0
  simp
  field_simp [n.cast_ne_zero.2 h0]
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

variable [IsProbabilityMeasure P]

lemma tendsto_charFun_inv_sqrt_mul_pow {X : Ω → ℝ}
    (hX : AEMeasurable X P) (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) (t : ℝ) :
    Tendsto (fun (n : ℕ) ↦ (charFun (P.map X) ((√n)⁻¹ * t)) ^ n) atTop
      (𝓝 (exp (-t ^ 2 / 2))) := by
  apply tendsto_pow_exp_of_isLittleO_sub_add_div_compat
  suffices (fun (n : ℕ) ↦ charFun (Measure.map X P) ((√n)⁻¹ * t) -
      (1 + (-(((√n)⁻¹ * t) ^ 2 / 2) : ℂ))) =o[atTop] fun n ↦ ((√n)⁻¹ * t) ^ 2 by
    have aux : (fun (n : ℕ) ↦ ‖(1 / n : ℂ)‖) = fun (n : ℕ) ↦ ‖(1 / n : ℝ)‖ := by simp
    rw [← Asymptotics.isLittleO_norm_right, aux, Asymptotics.isLittleO_norm_right]
    refine .of_const_mul_right (c := t ^ 2) ?_
    convert this using 4 with n <;> norm_cast <;> simp [field]
  have ht : Tendsto (fun (n : ℕ) ↦ (√n)⁻¹ * t) atTop (𝓝 0) := by
    rw [← zero_mul t]
    exact .mul_const t (tendsto_inv_atTop_zero.comp <| Real.tendsto_sqrt_atTop.comp <|
      tendsto_natCast_atTop_atTop)
  convert (taylor_charFun_two hX h0 h1).comp_tendsto ht using 2
  simp
  ring

end ProbabilityTheory
