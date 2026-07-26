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

import FormalConjectures.Other.SICLowDimAudit

/-!
# Qutrit Hesse SIC-POVM proof audit

A focused finite verification of the Hesse SIC family in dimension three.
-/

namespace OpenQuantumProblem23

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

private lemma q3_hesseS_sq : hesseS ^ (2 : ℕ) = (1 / 2 : ℝ) := by
  unfold hesseS
  nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (1 / 2 : ℝ))]

@[simp] private lemma q3_hesseS_mul_self : hesseS * hesseS = (1 / 2 : ℝ) := by
  simpa [pow_two] using q3_hesseS_sq

@[simp] private lemma q3_hesseS_sq_complex :
    ((hesseS : ℂ) * hesseS) = (1 / 2 : ℂ) := by
  have h : (((hesseS * hesseS : ℝ)) : ℂ) = (1 / 2 : ℂ) := by
    norm_num [q3_hesseS_mul_self]
  simpa only [Complex.ofReal_mul] using h

private lemma q3_sqrt_three_sq : (Real.sqrt 3) ^ (2 : ℕ) = (3 : ℝ) := by
  nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (3 : ℝ))]

private lemma q3_omega_sq :
    ω ^ 2 = ((-(1 : ℝ) / 2 : ℝ) : ℂ) -
      ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [ω, pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sub_re]
    nlinarith [q3_sqrt_three_sq]
  · simp [ω, pow_two, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_im]
    ring_nf

private lemma q3_explicit_omega_sq :
    (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I) = ω ^ 2 := by
  rw [q3_omega_sq]
  apply Complex.ext <;> simp <;> ring

@[simp] private lemma q3_star_omega : star ω = ω ^ 2 := by
  rw [q3_omega_sq]
  apply Complex.ext <;> simp [ω]

@[simp] private lemma q3_star_omega_sq : star (ω ^ 2) = ω := by
  rw [q3_omega_sq]
  apply Complex.ext <;> simp [ω]

@[simp] private lemma q3_omega_cubed : ω ^ 3 = 1 := by
  calc
    ω ^ 3 = ω * (ω ^ 2) := by ring
    _ = 1 := by
      rw [q3_omega_sq]
      apply Complex.ext
      · simp [ω, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sub_re]
        nlinarith [q3_sqrt_three_sq]
      · simp [ω, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_im]
        ring_nf

@[simp] private lemma q3_omega_four : ω ^ 4 = ω := by
  calc
    ω ^ 4 = ω ^ 3 * ω := by ring
    _ = ω := by simp

@[simp] private lemma q3_omega_mul_omega_sq : ω * (ω ^ 2) = 1 := by
  calc
    ω * (ω ^ 2) = ω ^ 3 := by ring
    _ = 1 := q3_omega_cubed

@[simp] private lemma q3_omega_sq_mul_omega : (ω ^ 2) * ω = 1 := by
  calc
    (ω ^ 2) * ω = ω ^ 3 := by ring
    _ = 1 := q3_omega_cubed

@[simp] private lemma q3_omega_sq_mul_omega_sq : (ω ^ 2) * (ω ^ 2) = ω := by
  calc
    (ω ^ 2) * (ω ^ 2) = ω ^ 4 := by ring
    _ = ω := q3_omega_four

@[simp] private lemma q3_omega_normSq : Complex.normSq ω = 1 := by
  rw [ω, Complex.normSq_add_mul_I]
  nlinarith [q3_sqrt_three_sq]

@[simp] private lemma q3_omega_sq_normSq : Complex.normSq (ω ^ 2) = 1 := by
  simp [pow_two, Complex.normSq_mul]

@[simp] private lemma q3_explicit_omega_sq_normSq :
    Complex.normSq (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I) = 1 := by
  rw [q3_explicit_omega_sq]
  exact q3_omega_sq_normSq

@[simp] private lemma q3_normSq_one_add_omega : Complex.normSq (1 + ω) = 1 := by
  have hrewrite :
      1 + ω = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
    simp [ω]
    ring
  rw [hrewrite, Complex.normSq_add_mul_I]
  nlinarith [q3_sqrt_three_sq]

@[simp] private lemma q3_normSq_one_add_omega_sq :
    Complex.normSq (1 + ω ^ 2) = 1 := by
  rw [q3_omega_sq]
  have hrewrite :
      1 + (((-(1 : ℝ) / 2 : ℝ) : ℂ) -
        ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I) =
        ((1 / 2 : ℝ) : ℂ) + ((-(Real.sqrt 3) / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  rw [hrewrite, Complex.normSq_add_mul_I]
  nlinarith [q3_sqrt_three_sq]

@[simp] private lemma q3_normSq_half :
    Complex.normSq (1 / 2 : ℂ) = (1 / 4 : ℝ) := by
  norm_num [Complex.normSq_ofReal]

@[simp] private lemma q3_normSq_half_mul_omega :
    Complex.normSq ((1 / 2 : ℂ) * ω) = (1 / 4 : ℝ) := by
  rw [Complex.normSq_mul, q3_omega_normSq]
  norm_num [Complex.normSq_ofReal]

@[simp] private lemma q3_normSq_half_mul_omega_sq :
    Complex.normSq ((1 / 2 : ℂ) * (ω ^ 2)) = (1 / 4 : ℝ) := by
  rw [Complex.normSq_mul, q3_omega_sq_normSq]
  norm_num [Complex.normSq_ofReal]

@[simp] private lemma q3_normSq_half_mul_one_add_omega :
    Complex.normSq ((1 / 2 : ℂ) * (1 + ω)) = (1 / 4 : ℝ) := by
  rw [Complex.normSq_mul, q3_normSq_one_add_omega]
  norm_num [Complex.normSq_ofReal]

@[simp] private lemma q3_normSq_half_mul_one_add_omega_sq :
    Complex.normSq ((1 / 2 : ℂ) * (1 + ω ^ 2)) = (1 / 4 : ℝ) := by
  rw [Complex.normSq_mul, q3_normSq_one_add_omega_sq]
  norm_num [Complex.normSq_ofReal]

@[simp] private lemma q3_normSq_half_add_half_mul_omega :
    Complex.normSq ((1 / 2 : ℂ) + (1 / 2 : ℂ) * ω) = (1 / 4 : ℝ) := by
  have h :
      ((1 / 2 : ℂ) + (1 / 2 : ℂ) * ω) = (1 / 2 : ℂ) * (1 + ω) := by ring
  rw [h]
  exact q3_normSq_half_mul_one_add_omega

@[simp] private lemma q3_normSq_half_add_half_mul_omega_sq :
    Complex.normSq ((1 / 2 : ℂ) + (1 / 2 : ℂ) * (ω ^ 2)) = (1 / 4 : ℝ) := by
  have h :
      ((1 / 2 : ℂ) + (1 / 2 : ℂ) * (ω ^ 2)) =
        (1 / 2 : ℂ) * (1 + ω ^ 2) := by ring
  rw [h]
  exact q3_normSq_half_mul_one_add_omega_sq

@[simp] private lemma q3_normSq_half_add_half_mul_explicit_omega_sq :
    Complex.normSq ((1 / 2 : ℂ) + (1 / 2 : ℂ) *
      (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I)) = (1 / 4 : ℝ) := by
  rw [q3_explicit_omega_sq]
  exact q3_normSq_half_add_half_mul_omega_sq

@[simp] private lemma q3_normSq_half_mul_omega_add_half :
    Complex.normSq ((1 / 2 : ℂ) * ω + (1 / 2 : ℂ)) = (1 / 4 : ℝ) := by
  simpa [add_comm] using q3_normSq_half_add_half_mul_omega

@[simp] private lemma q3_normSq_half_mul_explicit_omega_sq_add_half :
    Complex.normSq ((1 / 2 : ℂ) *
      (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I) + (1 / 2 : ℂ)) =
      (1 / 4 : ℝ) := by
  simpa [add_comm] using q3_normSq_half_add_half_mul_explicit_omega_sq

@[simp] private lemma q3_hesseS_sq_mul (z : ℂ) :
    (hesseS : ℂ) * ((hesseS : ℂ) * z) = (1 / 2 : ℂ) * z := by
  calc
    (hesseS : ℂ) * ((hesseS : ℂ) * z) = ((hesseS : ℂ) * hesseS) * z := by ring
    _ = (1 / 2 : ℂ) * z := by rw [q3_hesseS_sq_complex]

@[simp] private lemma q3_hesseS_mul_mul_hesseS (z : ℂ) :
    (hesseS : ℂ) * z * (hesseS : ℂ) = (1 / 2 : ℂ) * z := by
  calc
    (hesseS : ℂ) * z * (hesseS : ℂ) = ((hesseS : ℂ) * hesseS) * z := by ring
    _ = (1 / 2 : ℂ) * z := by rw [q3_hesseS_sq_complex]

@[simp] private lemma q3_normSq_half_add_hesseS_star_omega_mul_hesseS :
    Complex.normSq ((1 / 2 : ℂ) + (hesseS : ℂ) * (starRingEnd ℂ) ω *
      (hesseS : ℂ)) = (1 / 4 : ℝ) := by
  change Complex.normSq ((1 / 2 : ℂ) + (hesseS : ℂ) * star ω * (hesseS : ℂ)) =
    (1 / 4 : ℝ)
  rw [q3_star_omega, q3_hesseS_mul_mul_hesseS]
  exact q3_normSq_half_add_half_mul_omega_sq

@[simp] private lemma q3_normSq_half_add_hesseS_omega_mul_hesseS :
    Complex.normSq ((1 / 2 : ℂ) + (hesseS : ℂ) * ω * (hesseS : ℂ)) =
      (1 / 4 : ℝ) := by
  rw [q3_hesseS_mul_mul_hesseS]
  exact q3_normSq_half_add_half_mul_omega

@[simp] private lemma q3_normSq_half_add_hesseS_omega_mul_hesseS_omega :
    Complex.normSq ((1 / 2 : ℂ) + (hesseS : ℂ) * ω *
      ((hesseS : ℂ) * ω)) = (1 / 4 : ℝ) := by
  have hphase :
      (hesseS : ℂ) * ω * ((hesseS : ℂ) * ω) = (1 / 2 : ℂ) * (ω ^ 2) := by
    calc
      (hesseS : ℂ) * ω * ((hesseS : ℂ) * ω) =
          ((hesseS : ℂ) * hesseS) * (ω ^ 2) := by ring
      _ = (1 / 2 : ℂ) * (ω ^ 2) := by rw [q3_hesseS_sq_complex]
  rw [hphase]
  exact q3_normSq_half_add_half_mul_omega_sq

@[simp] private lemma q3_normSq_half_add_hesseS_star_omega_mul_hesseS_explicit_sq :
    Complex.normSq ((1 / 2 : ℂ) + (hesseS : ℂ) * (starRingEnd ℂ) ω *
      ((hesseS : ℂ) *
        (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I))) =
      (1 / 4 : ℝ) := by
  change Complex.normSq ((1 / 2 : ℂ) + (hesseS : ℂ) * star ω *
    ((hesseS : ℂ) *
      (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I))) = (1 / 4 : ℝ)
  rw [q3_star_omega, q3_explicit_omega_sq]
  ring_nf
  simpa only [pow_two, q3_hesseS_sq_complex, q3_omega_four] using
    q3_normSq_half_add_half_mul_omega

@[simp] private lemma q3_normSq_hesseS_star_omega_mul_hesseS_add_half :
    Complex.normSq ((hesseS : ℂ) * (starRingEnd ℂ) ω * (hesseS : ℂ) +
      (1 / 2 : ℂ)) = (1 / 4 : ℝ) := by
  simpa [add_comm] using q3_normSq_half_add_hesseS_star_omega_mul_hesseS

@[simp] private lemma q3_normSq_hesseS_omega_mul_hesseS_add_half :
    Complex.normSq ((hesseS : ℂ) * ω * (hesseS : ℂ) + (1 / 2 : ℂ)) =
      (1 / 4 : ℝ) := by
  simpa [add_comm] using q3_normSq_half_add_hesseS_omega_mul_hesseS

@[simp] private lemma q3_normSq_hesseS_omega_mul_hesseS_omega_add_half :
    Complex.normSq ((hesseS : ℂ) * ω * ((hesseS : ℂ) * ω) + (1 / 2 : ℂ)) =
      (1 / 4 : ℝ) := by
  simpa [add_comm] using q3_normSq_half_add_hesseS_omega_mul_hesseS_omega

@[simp] private lemma q3_normSq_hesseS_star_omega_mul_hesseS_explicit_sq_add_half :
    Complex.normSq ((hesseS : ℂ) * (starRingEnd ℂ) ω *
      ((hesseS : ℂ) *
        (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I)) +
      (1 / 2 : ℂ)) = (1 / 4 : ℝ) := by
  simpa [add_comm] using q3_normSq_half_add_hesseS_star_omega_mul_hesseS_explicit_sq

set_option maxHeartbeats 1000000 in
@[category test, AMS 15 47 81]
lemma hesseFamily_pairwise_audit2 :
    HasConstantOverlapSq (sicOverlapSq 3) hesseFamily := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  interval_cases i <;> interval_cases j
  all_goals
    simp [hesseFamily, vec3, overlapSq, sicOverlapSq, Fin.sum_univ_three] at hij ⊢
    first
      | done
      | contradiction
      | norm_num [sicOverlapSq]

@[category test, AMS 15 47 81]
theorem hasSICPOVM_three_audit2 : HasSICPOVM 3 := by
  refine ⟨hesseFamily, ?_⟩
  exact ⟨hesseFamily_normalized, hesseFamily_pairwise_audit2⟩

end OpenQuantumProblem23
