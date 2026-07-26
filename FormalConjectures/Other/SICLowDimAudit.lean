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

import FormalConjectures.OpenQuantumProblems.«23»

/-!
# Low-dimensional SIC-POVM proof audit

A focused proof of the tetrahedral qubit SIC benchmark using exact algebraic identities.
-/

namespace OpenQuantumProblem23

private lemma tetraA_sq_audit : tetraA ^ (2 : ℕ) = (1 / 3 : ℝ) := by
  unfold tetraA
  nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (1 / 3 : ℝ))]

private lemma tetraB_sq_audit : tetraB ^ (2 : ℕ) = (2 / 3 : ℝ) := by
  unfold tetraB
  nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (2 / 3 : ℝ))]

@[simp] private lemma tetraA_mul_self_audit : tetraA * tetraA = (1 / 3 : ℝ) := by
  simpa [pow_two] using tetraA_sq_audit

@[simp] private lemma tetraB_mul_self_audit : tetraB * tetraB = (2 / 3 : ℝ) := by
  simpa [pow_two] using tetraB_sq_audit

@[simp] private lemma tetraA_sq_complex_audit :
    ((tetraA : ℂ) * tetraA) = (1 / 3 : ℂ) := by
  exact_mod_cast tetraA_mul_self_audit

@[simp] private lemma tetraB_sq_complex_audit :
    ((tetraB : ℂ) * tetraB) = (2 / 3 : ℂ) := by
  exact_mod_cast tetraB_mul_self_audit

private lemma sq_sqrt_three_audit : (Real.sqrt 3) ^ (2 : ℕ) = (3 : ℝ) := by
  nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (3 : ℝ))]

@[simp] private lemma omega_sq_audit :
    ω ^ 2 = ((-(1 : ℝ) / 2 : ℝ) : ℂ) -
      ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [ω, pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sub_re]
    nlinarith [sq_sqrt_three_audit]
  · simp [ω, pow_two, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_im]
    ring_nf

@[simp] private lemma star_omega_audit : star ω = ω ^ 2 := by
  rw [omega_sq_audit]
  apply Complex.ext <;> simp [ω]

@[simp] private lemma star_omega_sq_audit : star (ω ^ 2) = ω := by
  rw [omega_sq_audit]
  apply Complex.ext <;> simp [ω]

@[simp] private lemma omega_cubed_audit : ω ^ 3 = 1 := by
  calc
    ω ^ 3 = ω * (ω ^ 2) := by ring
    _ = 1 := by
      rw [omega_sq_audit]
      apply Complex.ext
      · simp [ω, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sub_re]
        nlinarith [sq_sqrt_three_audit]
      · simp [ω, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_im]
        ring_nf

@[simp] private lemma omega_four_audit : ω ^ 4 = ω := by
  calc
    ω ^ 4 = ω ^ 3 * ω := by ring
    _ = ω := by simp

@[simp] private lemma omega_mul_omega_sq_audit : ω * (ω ^ 2) = 1 := by
  calc
    ω * (ω ^ 2) = ω ^ 3 := by ring
    _ = 1 := omega_cubed_audit

@[simp] private lemma omega_sq_mul_omega_audit : (ω ^ 2) * ω = 1 := by
  calc
    (ω ^ 2) * ω = ω ^ 3 := by ring
    _ = 1 := omega_cubed_audit

@[simp] private lemma omega_sq_mul_omega_sq_audit : (ω ^ 2) * (ω ^ 2) = ω := by
  calc
    (ω ^ 2) * (ω ^ 2) = ω ^ 4 := by ring
    _ = ω := omega_four_audit

@[simp] private lemma normSq_one_add_two_mul_omega_audit :
    Complex.normSq (1 + 2 * ω) = 3 := by
  have hrewrite :
      1 + 2 * ω = ((0 : ℝ) : ℂ) + ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [ω] <;> ring
  rw [hrewrite, Complex.normSq_add_mul_I]
  nlinarith [sq_sqrt_three_audit]

@[simp] private lemma normSq_one_add_two_mul_omega_sq_audit :
    Complex.normSq (1 + 2 * (ω ^ 2)) = 3 := by
  rw [omega_sq_audit]
  have hrewrite :
      1 + 2 * (((-(1 : ℝ) / 2 : ℝ) : ℂ) -
        ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I) =
        ((0 : ℝ) : ℂ) + ((-(Real.sqrt 3) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  rw [hrewrite, Complex.normSq_add_mul_I]
  nlinarith [sq_sqrt_three_audit]

@[simp] private lemma normSq_qubit_offdiag_omega_audit :
    Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) * ω) = (1 / 3 : ℝ) := by
  have hrewrite :
      ((1 / 3 : ℂ) + (2 / 3 : ℂ) * ω) = (1 / 3 : ℂ) * (1 + 2 * ω) := by
    ring
  rw [hrewrite, Complex.normSq_mul, normSq_one_add_two_mul_omega_audit]
  norm_num [Complex.normSq_ofReal]

@[simp] private lemma normSq_qubit_offdiag_omega_sq_audit :
    Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) * (ω ^ 2)) = (1 / 3 : ℝ) := by
  have hrewrite :
      ((1 / 3 : ℂ) + (2 / 3 : ℂ) * (ω ^ 2)) =
        (1 / 3 : ℂ) * (1 + 2 * (ω ^ 2)) := by
    ring
  rw [hrewrite, Complex.normSq_mul, normSq_one_add_two_mul_omega_sq_audit]
  norm_num [Complex.normSq_ofReal]

@[category test, AMS 15 47 81]
lemma qubitSICFamily_pairwise_audit :
    HasConstantOverlapSq (sicOverlapSq 2) qubitSICFamily := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  interval_cases i <;> interval_cases j
  all_goals
    simp [qubitSICFamily, vec2, overlapSq, sicOverlapSq, Fin.sum_univ_two] at hij ⊢
    first
      | done
      | contradiction
      | norm_num [sicOverlapSq]

@[category test, AMS 15 47 81]
theorem hasSICPOVM_two_audit : HasSICPOVM 2 := by
  refine ⟨qubitSICFamily, ?_⟩
  exact ⟨qubitSICFamily_normalized, qubitSICFamily_pairwise_audit⟩

end OpenQuantumProblem23
