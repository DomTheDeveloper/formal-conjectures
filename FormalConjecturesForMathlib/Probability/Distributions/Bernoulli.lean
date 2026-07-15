/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Bernoulli probability measures

A minimal compatibility backport for the mathlib snapshot pinned by formal-conjectures.
-/

public section

open MeasureTheory Measure unitInterval
open scoped ENNReal

namespace ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] {x y : X} {p : I}

/-- The Bernoulli measure giving mass `p` to `x` and mass `1 - p` to `y`. -/
@[expose]
noncomputable def bernoulliMeasure (x y : X) (p : I) : Measure X :=
  toNNReal p • dirac x + toNNReal (σ p) • dirac y

@[inherit_doc]
scoped notation "Ber(" x ", " y ", " p ")" => bernoulliMeasure x y p

lemma bernoulliMeasure_def (x y : X) (p : I) :
    Ber(x, y, p) = toNNReal p • dirac x + toNNReal (σ p) • dirac y := rfl

instance isProbabilityMeasure_bernoulliMeasure : IsProbabilityMeasure Ber(x, y, p) where
  measure_univ := by simp [bernoulliMeasure_def]

@[simp]
lemma bernoulliMeasure_zero (x y : X) : bernoulliMeasure x y 0 = dirac y := by
  simp [bernoulliMeasure_def]

@[simp]
lemma bernoulliMeasure_one (x y : X) : bernoulliMeasure x y 1 = dirac x := by
  simp [bernoulliMeasure_def]

section Integral

variable {E : Type*} [NormedAddCommGroup E]

lemma integrable_bernoulliMeasure [MeasurableSingletonClass X]
    (x y : X) (p : I) (f : X → E) : Integrable f Ber(x, y, p) := by
  simp [bernoulliMeasure_def, integrable_add_measure, integrable_dirac,
    Integrable.smul_measure_nnreal]

variable [NormedSpace ℝ E] [CompleteSpace E]

lemma integral_bernoulliMeasure [MeasurableSingletonClass X]
    (x y : X) (p : I) (f : X → E) :
    ∫ z, f z ∂Ber(x, y, p) = (p : ℝ) • f x + (1 - p : ℝ) • f y := by
  rw [bernoulliMeasure_def, integral_add_measure]
  · simp [NNReal.smul_def]
  all_goals exact (integrable_dirac (by simp)).smul_measure_nnreal

end Integral

end ProbabilityTheory
