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

public import Mathlib

@[expose] public section

noncomputable section

open scoped Classical
open Polynomial Module

namespace Nat

/-- The product of two squarefree natural numbers is a square only when they are equal. -/
theorem eq_of_squarefree_of_isSquare_mul {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hab : IsSquare (a * b)) : a = b := by
  apply (Squarefree.ext_iff ha hb).2
  intro p hp
  obtain ⟨c, hc⟩ := hab
  have hfac : a.factorization p + b.factorization p = 2 * c.factorization p := by
    calc
      a.factorization p + b.factorization p = (a * b).factorization p := by
        have h := congrArg (fun f : ℕ →₀ ℕ => f p)
          (factorization_mul ha.ne_zero hb.ne_zero).symm
        simpa using h
      _ = (c ^ 2).factorization p := by
        simpa [pow_two, hc]
      _ = 2 * c.factorization p := by simp [factorization_pow]
  constructor
  · intro hpa
    have hfa : a.factorization p = 1 := factorization_eq_one_of_squarefree ha hp hpa
    have hfb_le : b.factorization p ≤ 1 := hb.natFactorization_le_one p
    have hfb : b.factorization p = 1 := by omega
    exact (hp.dvd_iff_one_le_factorization hb.ne_zero).2 (by omega)
  · intro hpb
    have hfb : b.factorization p = 1 := factorization_eq_one_of_squarefree hb hp hpb
    have hfa_le : a.factorization p ≤ 1 := ha.natFactorization_le_one p
    have hfa : a.factorization p = 1 := by omega
    exact (hp.dvd_iff_one_le_factorization ha.ne_zero).2 (by omega)

end Nat

namespace Real

/-- In a number field, a non-rational element whose square is rational has trace zero. -/
theorem trace_eq_zero_of_sq_ratCast {K : Type*} [Field K] [NumberField K] {x : K} {r : ℚ}
    (hx2 : x ^ 2 = algebraMap ℚ K r) (hx : x ∉ (algebraMap ℚ K).range) :
    Algebra.trace ℚ K x = 0 := by
  have hmonic : (X ^ 2 - C r).Monic := Polynomial.monic_X_pow_sub_C r (by norm_num)
  have haeval : aeval x (X ^ 2 - C r : ℚ[X]) = 0 := by simp [hx2]
  have hdvd : minpoly ℚ x ∣ (X ^ 2 - C r) := minpoly.dvd ℚ x haeval
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hne : (X ^ 2 - C r : ℚ[X]) ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by norm_num) r
  have hdeg2 : (minpoly ℚ x).natDegree = 2 := by
    have hle : (minpoly ℚ x).natDegree ≤ 2 := by
      have := Polynomial.natDegree_le_of_dvd hdvd hne
      simpa [Polynomial.natDegree_X_pow_sub_C] using this
    have hge : 2 ≤ (minpoly ℚ x).natDegree := by
      by_contra h
      push_neg at h
      interval_cases hh : (minpoly ℚ x).natDegree
      · exact (minpoly.natDegree_pos hint).ne' hh
      · exact hx (minpoly.natDegree_eq_one_iff.mp hh)
    omega
  have heq_rev : X ^ 2 - C r = minpoly ℚ x :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (p := minpoly ℚ x) (q := X ^ 2 - C r)
      (minpoly.monic hint) hmonic hdvd
      (by rw [hdeg2, Polynomial.natDegree_X_pow_sub_C])
  have heq : minpoly ℚ x = X ^ 2 - C r := heq_rev.symm
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, heq]
  have hnc : (X ^ 2 - C r : ℚ[X]).nextCoeff = 0 := by
    rw [Polynomial.nextCoeff_of_natDegree_pos
      (by rw [Polynomial.natDegree_X_pow_sub_C]; norm_num)]
    simp [Polynomial.coeff_X_pow]
  rw [hnc]
  simp

/-- Square roots of an injective finite family of squarefree natural numbers are
linearly independent over the rationals. -/
theorem linearIndependent_sqrt_squarefree {ι : Type*} [Fintype ι]
    (s : ι → ℕ) (hs : ∀ i, Squarefree (s i)) (hinj : Function.Injective s) :
    LinearIndependent ℚ (fun i => Real.sqrt (s i)) := by
  let K : IntermediateField ℚ ℝ :=
    IntermediateField.adjoin ℚ (Set.range fun i => Real.sqrt (s i))
  have hfd : FiniteDimensional ℚ K := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro x ⟨i, rfl⟩
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (s i : ℚ),
      Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    norm_num [← Polynomial.C_pow]
  letI : NumberField K :=
    { to_charZero := inferInstance
      to_finiteDimensional := hfd }
  let root (i : ι) : K :=
    ⟨Real.sqrt (s i), IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩
  have hroot_sq (i : ι) : (root i) ^ 2 = algebraMap ℚ K (s i : ℚ) := by
    apply Subtype.ext
    change (Real.sqrt (s i : ℝ)) ^ 2 = (s i : ℝ)
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  have hmul_sq (i j : ι) : (root i * root j) ^ 2 = algebraMap ℚ K ((s i * s j : ℕ) : ℚ) := by
    rw [mul_pow, hroot_sq, hroot_sq, ← map_mul]
    norm_cast
  have hmul_not_range {i j : ι} (hij : i ≠ j) :
      root i * root j ∉ (algebraMap ℚ K).range := by
    intro h
    obtain ⟨q, hq⟩ := h
    have hsq_rat : IsSquare (((s i * s j : ℕ) : ℚ)) := by
      refine ⟨q, ?_⟩
      apply (algebraMap ℚ K).injective
      calc
        algebraMap ℚ K (((s i * s j : ℕ) : ℚ)) = (root i * root j) ^ 2 :=
          (hmul_sq i j).symm
        _ = (algebraMap ℚ K q) ^ 2 := by rw [← hq]
        _ = algebraMap ℚ K (q * q) := by rw [map_mul, pow_two]
    have hsq_nat : IsSquare (s i * s j) := by
      rwa [Rat.isSquare_natCast_iff] at hsq_rat
    exact hij (hinj (Nat.eq_of_squarefree_of_isSquare_mul (hs i) (hs j) hsq_nat))
  have htrace_mul_of_ne {i j : ι} (hij : i ≠ j) :
      Algebra.trace ℚ K (root i * root j) = 0 :=
    trace_eq_zero_of_sq_ratCast (hmul_sq i j) (hmul_not_range hij)
  have htrace_self (i : ι) :
      Algebra.trace ℚ K (root i * root i) = (finrank ℚ K : ℚ) * s i := by
    convert congr_arg (fun x : K => Algebra.trace ℚ K x) (hroot_sq i) using 1
    · rw [sq]
    · rw [Algebra.trace_algebraMap]
      norm_num [Algebra.smul_def]
  have htraceMatrix :
      Algebra.traceMatrix ℚ root = Matrix.diagonal (fun i => (finrank ℚ K : ℚ) * s i) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, htrace_self]
    · simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, h,
        htrace_mul_of_ne h]
  have hdiscr : Algebra.discr ℚ root ≠ 0 := by
    rw [Algebra.discr_def, htraceMatrix]
    simp only [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      mul_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt Module.finrank_pos))
        (Nat.cast_ne_zero.mpr (hs i).ne_zero)
  have hrootK : LinearIndependent ℚ root := by
    by_contra h
    exact hdiscr (Algebra.discr_zero_of_not_linearIndependent ℚ h)
  let inc : K →ₗ[ℚ] ℝ :=
    { toFun := fun x => x.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinc : LinearMap.ker inc = ⊥ := by
    ext x
    simp [inc]
  have himage := hrootK.map' inc hinc
  simpa [Function.comp_def, root, inc] using himage

end Real