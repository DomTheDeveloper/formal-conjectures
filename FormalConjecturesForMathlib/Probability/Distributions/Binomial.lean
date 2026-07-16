/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.NCard
public import Mathlib.Probability.Distributions.SetBernoulli

import Mathlib.Probability.Notation

/-!
# Binomial probability measures

Minimal compatibility backport for the mathlib snapshot pinned by formal-conjectures.
It defines the measure-valued binomial law and its finite-support integral formula.
-/

public section

open MeasureTheory Set Measure
open scoped NNReal ProbabilityTheory unitInterval ENNReal

namespace ProbabilityTheory

section SetBernoulliCompat

variable {ι : Type*} [Countable ι] {u : Set ι} {p : I}

lemma setBernoulli_apply_eq_apply_subsets (u : Set ι) (p : I) (S : Set (Set ι)) :
    setBer(u, p) S = setBer(u, p) {s ∈ S | s ⊆ u} := by
  apply (measure_eq_measure_of_null_sdiff (by grind) ?_).symm
  exact Measure.mono_null (by grind) setBernoulli_ae_subset

lemma map_ncard_setBernoulli_apply (u : Set ι) (p : I) (s : Set ℕ) :
    (setBer(u, p).map Set.ncard) s = setBer(u, p) {t ⊆ u | t.ncard ∈ s} := by
  rw [map_apply (by fun_prop) .of_discrete, setBernoulli_apply_eq_apply_subsets]
  simp [And.comm]

@[simp]
lemma setBernoulli_real_singleton (p : I) {s : Set ι} (hsu : s ⊆ u) (hu : u.Finite) :
    setBer(u, p).real {s} = p ^ s.ncard * (1 - p : ℝ) ^ (u \ s).ncard := by
  simp [measureReal_def, setBernoulli_singleton p hsu hu]

lemma map_ncard_setBernoulli_real_singleton {u : Set ι} (hu : u.Finite) (p : I) (k : ℕ) :
    (setBer(u, p).map Set.ncard).real {k} =
      (u.ncard.choose k) * p ^ k * (1 - p) ^ (u.ncard - k) := by
  have hfin : {s ⊆ u | s.ncard ∈ ({k} : Set ℕ)}.Finite :=
    hu.finite_subsets.subset (by grind)
  rw [measureReal_def, map_ncard_setBernoulli_apply, ← measureReal_def,
    ← Set.biUnion_of_singleton (setOf _)]
  simp_rw [← hfin.mem_toFinset]
  rw [measureReal_biUnion_finset (by simp) (by simp)]
  have h1 s (hs : s ∈ hfin.toFinset) :
      setBer(u, p).real {s} = p ^ k * (1 - p) ^ (u.ncard - k) := by
    simp only [Set.mem_singleton_iff, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hs
    rw [setBernoulli_real_singleton _ hs.1 hu, Set.ncard_sdiff' hs.1 hu, hs.2]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_assoc,
    ← Set.ncard_eq_toFinset_card _ _]
  simp [Set.ncard_powerset_ncard, hu]

lemma map_ncard_setBernoulli_singleton {u : Set ι} (hu : u.Finite) (p : I) (k : ℕ) :
    (setBer(u, p).map Set.ncard) {k} =
      ENNReal.ofReal ((u.ncard.choose k) * p ^ k * (1 - p) ^ (u.ncard - k)) := by
  rw [← ENNReal.ofReal_toReal (a := (Measure.map _ _) _) (by simp), ← measureReal_def,
    map_ncard_setBernoulli_real_singleton hu]

end SetBernoulliCompat

variable {R Ω : Type*} [MeasurableSpace R] [AddMonoidWithOne R] {m : MeasurableSpace Ω}
  {P : Measure Ω} {X : Ω → R} {n : ℕ} {p : I}

/-- The binomial probability distribution with parameters `n` and `p`. -/
@[expose]
noncomputable def binomial (n : ℕ) (p : I) : Measure ℕ := setBer(Iio n, p).map ncard

/-- The binomial probability distribution with parameters `n` and `p`. -/
scoped notation3 "Bin(" n ", " p ")" => binomial n p

/-- The binomial probability distribution valued in the semiring `R`. -/
scoped notation3 "Bin(" R ", " n ", " p ")" => (binomial n p).map (Nat.cast : ℕ → R)

@[simp]
lemma binomial_nat : Bin(ℕ, n, p) = Bin(n, p) := map_id

lemma binomial_zero : Bin(0, p) = dirac 0 := by simp [binomial]

@[simp]
lemma map_cast_binomial_zero : Bin(R, 0, p) = dirac 0 := by
  simp [binomial, map_dirac' .of_discrete]

instance isProbabilityMeasure_binomial : IsProbabilityMeasure Bin(n, p) :=
  isProbabilityMeasure_map <| by fun_prop

instance isProbabilityMeasure_map_cast_binomial : IsProbabilityMeasure Bin(R, n, p) :=
  isProbabilityMeasure_map .of_discrete

lemma binomial_real_singleton (n k : ℕ) (p : I) :
    Bin(n, p).real {k} = (n.choose k) * p ^ k * (1 - p) ^ (n - k) := by
  rw [binomial, map_ncard_setBernoulli_real_singleton (finite_Iio n), ncard_Iio_nat]

lemma binomial_singleton (n k : ℕ) (p : I) :
    Bin(n, p) {k} = ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) := by
  rw [← ENNReal.ofReal_toReal (a := Bin(n, p) _) (by simp), ← measureReal_def,
    binomial_real_singleton]

lemma map_cast_binomial_real_singleton [MeasurableSingletonClass R] [CharZero R]
    (n k : ℕ) (p : I) :
    Bin(R, n, p).real {(k : R)} = (n.choose k) * p ^ k * (1 - p) ^ (n - k) := by
  rw [map_measureReal_apply (by fun_prop) (by measurability)]
  convert binomial_real_singleton n k p
  ext
  simp

@[simp]
lemma binomial_nonneg {k : ℕ} :
    (0 : ℝ) ≤ (n.choose k) * p ^ k * (1 - p) ^ (n - k) :=
  mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by grind) _)) (pow_nonneg (by grind) _)

lemma map_cast_binomial_singleton [MeasurableSingletonClass R] [CharZero R]
    (n k : ℕ) (p : I) :
    Bin(R, n, p) {(k : R)} =
      ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) := by
  rw [← ENNReal.ofReal_toReal (a := Bin(R, n, p) _) (by simp), ← measureReal_def,
    map_cast_binomial_real_singleton]

@[simp]
lemma binomial_real_zero (n : ℕ) (p : I) : Bin(n, p).real {0} = (1 - p) ^ n := by
  simp [binomial_real_singleton]

@[simp]
lemma map_cast_binomial_real_zero [MeasurableSingletonClass R] [CharZero R]
    (n : ℕ) (p : I) : Bin(R, n, p).real {0} = (1 - p) ^ n := by
  rw [← Nat.cast_zero, map_cast_binomial_real_singleton]
  simp

@[simp]
lemma binomial_real_self (n : ℕ) (p : I) : Bin(n, p).real {n} = p ^ n := by
  simp [binomial_real_singleton]

@[simp]
lemma map_cast_binomial_real_self [MeasurableSingletonClass R] [CharZero R]
    (n : ℕ) (p : I) : Bin(R, n, p).real {(n : R)} = p ^ n := by
  simp [map_cast_binomial_real_singleton]

lemma binomial_eq_sum_dirac (n : ℕ) (p : I) :
    Bin(n, p) =
      ∑ k ∈ Finset.Iic n,
        ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) • dirac k := by
  refine ext_of_singleton fun k ↦ ?_
  rw [binomial_singleton, finsetSum_apply, Finset.sum_eq_single k]
  · simp
  · simp_all
  · simp_all [Nat.choose_eq_zero_of_lt]

lemma map_cast_binomial_eq_sum_dirac [MeasurableSingletonClass R] (n : ℕ) (p : I) :
    Bin(R, n, p) =
      ∑ k ∈ Finset.Iic n,
        ENNReal.ofReal ((n.choose k) * p ^ k * (1 - p) ^ (n - k)) • dirac (k : R) := by
  rw [binomial_eq_sum_dirac, Measure.map_finset_sum .of_discrete]
  exact Finset.sum_congr rfl fun _ _ ↦ by rw [Measure.map_smul, map_dirac]

section Integral

variable {E : Type*} [NormedAddCommGroup E]

lemma integrable_map_cast_binomial [MeasurableSingletonClass R] (f : R → E) :
    Integrable f Bin(R, n, p) := by
  simp [map_cast_binomial_eq_sum_dirac, integrable_finsetSum_measure, integrable_dirac,
    Integrable.smul_measure]

lemma integrable_binomial (f : ℕ → E) :
    Integrable f Bin(n, p) := (integrable_map_cast_binomial f).comp_measurable .of_discrete

variable [NormedSpace ℝ E] [CompleteSpace E]

lemma integral_binomial (f : ℕ → E) :
    ∫ x, f x ∂Bin(n, p) =
      ∑ k ∈ Finset.Iic n, (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) • f k := by
  rw [binomial_eq_sum_dirac, integral_finsetSum_measure]
  · simp
  exact fun _ _ ↦ (integrable_dirac (by simp)).smul_measure (by simp)

lemma integral_map_cast_binomial [MeasurableSingletonClass R] (f : R → E) :
    ∫ x, f x ∂Bin(R, n, p) =
      ∑ k ∈ Finset.Iic n, (n.choose k * (p : ℝ) ^ k * (1 - p) ^ (n - k)) • f k := by
  rw [integral_map .of_discrete (integrable_map_cast_binomial f).aestronglyMeasurable,
    integral_binomial]

end Integral

end ProbabilityTheory
