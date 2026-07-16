/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction
public import Mathlib.Probability.ProbabilityMassFunction.Binomial
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Topology.UnitInterval

/-!
# Binomial probability measures

Minimal compatibility layer for the mathlib snapshot pinned by formal-conjectures. The snapshot
already contains a normalized binomial probability mass function on `Fin (n + 1)`. We push that
PMF to `ℕ`, and then to any measurable additive monoid via the natural-number cast.
-/

public section

open MeasureTheory Measure Complex unitInterval
open scoped unitInterval

namespace ProbabilityTheory

variable {R : Type*} [MeasurableSpace R] [AddMonoidWithOne R] {n : ℕ} {p : I}

@[expose]
noncomputable def binomialPMF (n : ℕ) (p : I) : PMF (Fin (n + 1)) :=
  PMF.binomial (toNNReal p) (by simpa using p.2.2) n

/-- The binomial probability distribution with parameters `n` and `p`. -/
@[expose]
noncomputable def binomial (n : ℕ) (p : I) : Measure ℕ :=
  (binomialPMF n p).toMeasure.map Fin.val

/-- The binomial probability distribution on `ℕ`. -/
scoped notation3 "Bin(" n ", " p ")" => binomial n p

/-- The binomial probability distribution valued in the semiring `R`. -/
scoped notation3 "Bin(" R ", " n ", " p ")" => (binomial n p).map (Nat.cast : ℕ → R)

@[simp]
lemma binomial_nat : Bin(ℕ, n, p) = Bin(n, p) := map_id

instance isProbabilityMeasure_binomial : IsProbabilityMeasure Bin(n, p) :=
  isProbabilityMeasure_map (.of_discrete : Measurable (Fin.val : Fin (n + 1) → ℕ)).aemeasurable

instance isProbabilityMeasure_map_cast_binomial : IsProbabilityMeasure Bin(R, n, p) :=
  isProbabilityMeasure_map .of_discrete

lemma charFun_map_cast_binomial (n : ℕ) (p : I) (t : ℝ) :
    charFun Bin(ℝ, n, p) t =
      (((1 - (p : ℝ) : ℝ) : ℂ) + (p : ℂ) * exp (t * Complex.I)) ^ n := by
  rw [charFun_apply_real]
  change (∫ x : ℝ, exp (t * x * Complex.I) ∂((binomial n p).map (Nat.cast : ℕ → ℝ))) = _
  rw [integral_map, binomial, integral_map, PMF.integral_eq_sum]
  any_goals fun_prop
  simp only [binomialPMF, PMF.binomial_apply, Finset.sum_fin_eq_sum_range]
  rw [← add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  simp only [dif_pos hk]
  push_cast
  rw [← Complex.exp_nat_mul]
  ring

end ProbabilityTheory
