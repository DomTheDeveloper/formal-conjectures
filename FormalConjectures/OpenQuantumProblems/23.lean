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

import FormalConjectures.Util.ProblemImports

/-!
# Open Quantum Problem 23: SIC-POVMs

## Mathematical problem
The OQP page presents three increasingly strong formulations of this problem.
In this file we formalize the first one, closest to the physics terminology:
existence of a symmetric informationally complete POVM in every finite dimension.

A SIC-POVM in dimension $d$ can be represented by a family of $d^2$ normalized
vectors in $\mathbb{C}^d$ whose pairwise squared overlaps are all equal to
$(d + 1)^{-1}$. We encode such a family as a map `Fin (d ^ 2) → StateVector d`.

## Background
SIC-POVMs are a basic structure in finite-dimensional quantum information.
They are closely related to equiangular lines, tight frames, quantum state
reconstruction, and finite-dimensional measurement theory.
The open problem asks whether such families exist in every dimension.

## What this file formalizes
This file formalizes the existence problem for symmetric informationally complete
POVMs through the predicate `HasSICPOVM d`.

More precisely, it contains the following layers.

### Core API
The main definitions formalized in this file are:
- `StateVector d`: a state vector in `ℂ^d`;
- `mkStateVector`: constructor from coordinates in the computational basis;
- `IsNormalized ψ`: normalization predicate for a state vector;
- `overlapSq φ ψ`: squared magnitude of the inner-product overlap;
- `HasConstantOverlapSq c Φ`: constant pairwise squared-overlap condition;
- `sicOverlapSq d`: the SIC overlap value `(d + 1)⁻¹`;
- `IsSICFamily d Φ`: the predicate that a family of `d^2` vectors in `ℂ^d`
  is a SIC family;
- `HasSICPOVM d`: existence of a SIC family in dimension `d`.

In addition, the file includes explicit witness families and convenient
constructors used in the low-dimensional benchmark cases:
- `vec2`, `vec3`;
- `qubitSICFamily`;
- `hesseFamily`;
- `bb84Family`.

### Complete open conjecture
The main open theorem is:
- `sicPOVMs`, expressing the conjecture that for every `d ≥ 1`, there exists a
  SIC-POVM in dimension `d`.

### Special cases
The file also isolates several special cases:
- solved low-dimensional benchmark cases:
  `hasSICPOVM_zero`, `hasSICPOVM_one`, `hasSICPOVM_two`, `hasSICPOVM_three`;
- a negative benchmark result:
  `bb84Family_not_isSICFamily`, showing that the BB84 family in dimension `2`
  does not form a SIC family;
- selected open benchmark dimensions:
  `hasSICPOVM_56`, `hasSICPOVM_58`, `hasSICPOVM_59`, `hasSICPOVM_60`,
  `hasSICPOVM_64`, `hasSICPOVM_68`, `hasSICPOVM_69`, `hasSICPOVM_70`,
  `hasSICPOVM_71`, `hasSICPOVM_72`, `hasSICPOVM_75`.

### Test lemmas
The file includes the following test lemmas and benchmark-support statements:
- `hasConstantOverlapSq_singleton`;
- `sicOverlapSq_one`, `sicOverlapSq_two`, `sicOverlapSq_three`,
  `sicOverlapSq_pos`;
- `isSICFamily_singleton_iff`, `isSICFamily_one_of_normalized`;
- `qubitSICFamily_normalized`, `qubitSICFamily_pairwise`;
- `hesseFamily_normalized`, `hesseFamily_pairwise`;
- `bb84Family_normalized`.

The low-dimensional dimension-$2$ and dimension-$3$ benchmark results are proved by
exact finite algebraic verification of the tetrahedral and Hesse witness families.

## References
*Primary source list entry:*
- IQOQI Vienna Open Quantum Problems, problem 23:
  https://oqp.iqoqi.oeaw.ac.at/sic-povms-and-zauners-conjecture
- Formal Conjectures issue #1823:
  https://github.com/google-deepmind/formal-conjectures/issues/1823

### Foundational references
- J. M. Renes, R. Blume-Kohout, A. J. Scott, and M. C. Caves,
  *Symmetric informationally complete quantum measurements*,
  J. Math. Phys. 45, 2171-2180 (2004), arXiv:quant-ph/0310075.
- G. Zauner,
  *Quantum Designs: Foundations of a Noncommutative Design Theory*,
  PhD thesis, University of Vienna (1999).
-/
noncomputable section
namespace OpenQuantumProblem23

/- ## Basic structures -/

/-- A state vector in the $d$-dimensional complex Hilbert space $\mathbb{C}^d$. -/
abbrev StateVector (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- Build a state vector from its coordinates in the computational basis. -/
abbrev mkStateVector {d : ℕ} (ψ : Fin d → ℂ) : StateVector d := WithLp.toLp 2 ψ

/-- Coercion from a state vector to its coordinate function. -/
instance {d : ℕ} : CoeFun (StateVector d) (fun _ => Fin d → ℂ) where
  coe ψ := ψ.ofLp

/-- A state vector is normalized if it has $L^2$ norm $1$. -/
def IsNormalized {d : ℕ} (ψ : StateVector d) : Prop := ‖ψ‖ = 1

/-- The squared magnitude of the overlap between two state vectors. -/
def overlapSq {d : ℕ} (φ ψ : StateVector d) : ℝ :=
  Complex.normSq (∑ i : Fin d, star (φ i) * ψ i)

/-- A family has constant pairwise squared overlap $c$ if every two distinct members have squared overlap $c$. -/
def HasConstantOverlapSq {d N : ℕ} (c : ℝ) (Φ : Fin N → StateVector d) : Prop :=
  Pairwise fun i j => overlapSq (Φ i) (Φ j) = c

/-- The squared overlap value of a SIC family in dimension $d$. -/
def sicOverlapSq (d : ℕ) : ℝ := (d + 1 : ℝ)⁻¹

/-- A SIC family in dimension $d$ consists of $d^2$ normalized vectors in $\mathbb{C}^d$ with pairwise squared overlap $(d + 1)^{-1}$. -/
def IsSICFamily (d : ℕ) (Φ : Fin (d ^ 2) → StateVector d) : Prop :=
  (∀ i, IsNormalized (Φ i)) ∧ HasConstantOverlapSq (sicOverlapSq d) Φ

/-- There exists a SIC-POVM in dimension $d$. -/
def HasSICPOVM (d : ℕ) : Prop :=
  ∃ Φ : Fin (d ^ 2) → StateVector d, IsSICFamily d Φ

/- ## Basic benchmark cases -/

/-- Any singleton family has constant pairwise squared overlap, vacuously. -/
@[category test, AMS 15 47 81]
lemma hasConstantOverlapSq_singleton {d : ℕ} (c : ℝ) (ψ : StateVector d) :
    HasConstantOverlapSq c (fun _ : Fin 1 => ψ) := by
  intro i j hij
  exact absurd (Subsingleton.elim i j) hij

/-- The SIC overlap value in dimension $1$ is $1/2$. -/
@[category test, AMS 15 47 81]
lemma sicOverlapSq_one : sicOverlapSq 1 = (1 / 2 : ℝ) := by
  simp [sicOverlapSq]; norm_num

/-- The SIC overlap value is positive in every dimension. -/
@[category test, AMS 15 47 81]
lemma sicOverlapSq_pos (d : ℕ) : 0 < sicOverlapSq d := by
  simp [sicOverlapSq]; positivity

/-- In dimension $1$, a singleton family is SIC exactly when its vector is normalized. -/
@[category test, AMS 15 47 81]
lemma isSICFamily_singleton_iff {ψ : StateVector 1} :
    IsSICFamily 1 (fun _ : Fin 1 => ψ) ↔ IsNormalized ψ := by
  constructor
  · intro ⟨h, _⟩; exact h 0
  · intro h; exact ⟨fun _ => h, hasConstantOverlapSq_singleton _ _⟩

/-- The empty family witnesses the degenerate dimension-$0$ case. -/
@[category test, AMS 15 47 81]
theorem hasSICPOVM_zero : HasSICPOVM 0 := by
  exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i j _ => Fin.elim0 i⟩

/-- Any normalized state in dimension $1$ yields a SIC family. -/
@[category test, AMS 15 47 81]
lemma isSICFamily_one_of_normalized {ψ : StateVector 1} (hψ : IsNormalized ψ) :
    IsSICFamily 1 (fun _ : Fin 1 => ψ) :=
  isSICFamily_singleton_iff.mpr hψ

/-- Dimension $1$ admits a SIC-POVM. -/
@[category test, AMS 15 47 81]
theorem hasSICPOVM_one : HasSICPOVM 1 := by
  refine ⟨fun _ => EuclideanSpace.single 0 1, isSICFamily_one_of_normalized ?_⟩
  simp [IsNormalized, EuclideanSpace.norm_single]

/- ## Explicit low-dimensional witnesses -/

/-- The standard algebraic primitive cube root of unity. -/
def ω : ℂ :=
  ((-(1 : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I

/-- The first real amplitude used in the tetrahedral qubit SIC. -/
def tetraA : ℝ := Real.sqrt (1 / 3)

/-- The second real amplitude used in the tetrahedral qubit SIC. -/
def tetraB : ℝ := Real.sqrt (2 / 3)

/-- The common scale used in the Hesse qutrit SIC. -/
def hesseS : ℝ := Real.sqrt (1 / 2)

/-- A convenient constructor for qubit state vectors. -/
def vec2 (z₀ z₁ : ℂ) : StateVector 2 := mkStateVector ![z₀, z₁]

/-- A convenient constructor for qutrit state vectors. -/
def vec3 (z₀ z₁ z₂ : ℂ) : StateVector 3 := mkStateVector ![z₀, z₁, z₂]

/-- The tetrahedral qubit SIC family. -/
def qubitSICFamily : Fin 4 → StateVector 2
  | 0 => vec2 1 0
  | 1 => vec2 (tetraA : ℂ) (tetraB : ℂ)
  | 2 => vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω)
  | _ => vec2 (tetraA : ℂ) ((tetraB : ℂ) * (ω ^ 2))

/-- The Hesse qutrit SIC family. -/
def hesseFamily : Fin 9 → StateVector 3
  | 0 => vec3 0 (hesseS : ℂ) (-(hesseS : ℂ))
  | 1 => vec3 0 (hesseS : ℂ) (-((hesseS : ℂ) * ω))
  | 2 => vec3 0 (hesseS : ℂ) (-((hesseS : ℂ) * (ω ^ 2)))
  | 3 => vec3 (-(hesseS : ℂ)) 0 (hesseS : ℂ)
  | 4 => vec3 (-((hesseS : ℂ) * ω)) 0 (hesseS : ℂ)
  | 5 => vec3 (-((hesseS : ℂ) * (ω ^ 2))) 0 (hesseS : ℂ)
  | 6 => vec3 (hesseS : ℂ) (-(hesseS : ℂ)) 0
  | 7 => vec3 (hesseS : ℂ) (-((hesseS : ℂ) * ω)) 0
  | _ => vec3 (hesseS : ℂ) (-((hesseS : ℂ) * (ω ^ 2))) 0

/-- The BB84 family of four qubit states. -/
def bb84Family : Fin 4 → StateVector 2
  | 0 => vec2 1 0
  | 1 => vec2 0 1
  | 2 => vec2 (hesseS : ℂ) (hesseS : ℂ)
  | _ => vec2 (hesseS : ℂ) (-(hesseS : ℂ))

/-- The SIC overlap value in dimension $2$ is $1/3$. -/
@[category test, AMS 15 47 81]
lemma sicOverlapSq_two : sicOverlapSq 2 = (1 / 3 : ℝ) := by
  simp [sicOverlapSq]; norm_num

/-- The SIC overlap value in dimension $3$ is $1/4$. -/
@[category test, AMS 15 47 81]
lemma sicOverlapSq_three : sicOverlapSq 3 = (1 / 4 : ℝ) := by
  simp [sicOverlapSq]; norm_num

/-- The unit complex number `ω` (primitive cube root) has norm `1`. -/
@[category API, AMS 15 47 81]
private lemma omega_norm : ‖ω‖ = 1 := by
  rw [Complex.norm_def, ω]
  simp [Complex.normSq_apply]
  have : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [show (-1 / 2 : ℝ) * (-1 / 2) + Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 1
    from by nlinarith]

/-- Every vector in the tetrahedral qubit SIC family is normalized. -/
@[category test, AMS 15 47 81]
lemma qubitSICFamily_normalized (i : Fin 4) :
    IsNormalized (qubitSICFamily i) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have sqrt2_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have sqrt3_pos : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have omega2_norm : ‖ω ^ 2‖ = 1 := by rw [norm_pow, omega_norm]; ring
  fin_cases i <;>
    simp [IsNormalized, qubitSICFamily, vec2, mkStateVector,
      EuclideanSpace.norm_eq, Fin.sum_univ_two, tetraA, tetraB,
      omega_norm, omega2_norm, abs_of_pos sqrt2_pos, abs_of_pos sqrt3_pos]
  all_goals (try (field_simp; linarith [h2, h3]))

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
  have h : (((tetraA * tetraA : ℝ)) : ℂ) = (1 / 3 : ℂ) := by
    norm_num [tetraA_mul_self_audit]
  simpa only [Complex.ofReal_mul] using h

@[simp] private lemma tetraB_sq_complex_audit :
    ((tetraB : ℂ) * tetraB) = (2 / 3 : ℂ) := by
  have h : (((tetraB * tetraB : ℝ)) : ℂ) = (2 / 3 : ℂ) := by
    norm_num [tetraB_mul_self_audit]
  simpa only [Complex.ofReal_mul] using h

private lemma sq_sqrt_three_audit : (Real.sqrt 3) ^ (2 : ℕ) = (3 : ℝ) := by
  nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (3 : ℝ))]

private lemma omega_sq_audit :
    ω ^ 2 = ((-(1 : ℝ) / 2 : ℝ) : ℂ) -
      ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [ω, pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sub_re]
    nlinarith [sq_sqrt_three_audit]
  · simp [ω, pow_two, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_im]
    ring_nf

set_option linter.unnecessarySeqFocus false in
private lemma explicit_omega_sq_audit :
    (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I) = ω ^ 2 := by
  rw [omega_sq_audit]
  apply Complex.ext <;> simp <;> ring

@[simp] private lemma explicit_omega_audit :
    (-(1 : ℂ) / (starRingEnd ℂ) 2 +
      ((Real.sqrt 3 : ℂ) / (starRingEnd ℂ) 2) * Complex.I) = ω := by
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    change star (2 : ℂ) = 2
    simp
  rw [htwo]
  apply Complex.ext <;> simp [ω]

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

@[simp] private lemma tetraB_sq_mul_audit (z : ℂ) :
    (tetraB : ℂ) * ((tetraB : ℂ) * z) = (2 / 3 : ℂ) * z := by
  calc
    (tetraB : ℂ) * ((tetraB : ℂ) * z) = ((tetraB : ℂ) * tetraB) * z := by ring
    _ = (2 / 3 : ℂ) * z := by rw [tetraB_sq_complex_audit]

@[simp] private lemma tetraB_mul_mul_tetraB_audit (z : ℂ) :
    (tetraB : ℂ) * z * (tetraB : ℂ) = (2 / 3 : ℂ) * z := by
  calc
    (tetraB : ℂ) * z * (tetraB : ℂ) = ((tetraB : ℂ) * tetraB) * z := by ring
    _ = (2 / 3 : ℂ) * z := by rw [tetraB_sq_complex_audit]

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

@[simp] private lemma normSq_qubit_offdiag_explicit_omega_sq_audit :
    Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) *
      (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I)) = (1 / 3 : ℝ) := by
  rw [explicit_omega_sq_audit]
  exact normSq_qubit_offdiag_omega_sq_audit

@[simp] private lemma normSq_qubit_offdiag_star_omega_exact_audit :
    Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) * (starRingEnd ℂ) ω) =
      (1 / 3 : ℝ) := by
  change Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) * star ω) = (1 / 3 : ℝ)
  rw [star_omega_audit]
  exact normSq_qubit_offdiag_omega_sq_audit

@[simp] private lemma overlap_one_two_audit :
    Complex.normSq ((1 / 3 : ℂ) + (tetraB : ℂ) * ((tetraB : ℂ) * ω)) =
      (1 / 3 : ℝ) := by
  rw [tetraB_sq_mul_audit]
  exact normSq_qubit_offdiag_omega_audit

@[simp] private lemma overlap_one_three_audit :
    Complex.normSq ((1 / 3 : ℂ) + (tetraB : ℂ) *
      ((tetraB : ℂ) * (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I))) =
      (1 / 3 : ℝ) := by
  rw [explicit_omega_sq_audit, tetraB_sq_mul_audit]
  exact normSq_qubit_offdiag_omega_sq_audit

@[simp] private lemma overlap_two_one_audit :
    Complex.normSq ((1 / 3 : ℂ) + (tetraB : ℂ) * star ω * (tetraB : ℂ)) =
      (1 / 3 : ℝ) := by
  rw [star_omega_audit, tetraB_mul_mul_tetraB_audit]
  exact normSq_qubit_offdiag_omega_sq_audit

@[simp] private lemma overlap_two_three_audit :
    Complex.normSq ((1 / 3 : ℂ) + (tetraB : ℂ) * star ω *
      ((tetraB : ℂ) * (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I))) =
      (1 / 3 : ℝ) := by
  rw [star_omega_audit, explicit_omega_sq_audit]
  ring_nf
  simpa only [pow_two, tetraB_sq_complex_audit, omega_four_audit] using
    normSq_qubit_offdiag_omega_audit

@[simp] private lemma overlap_two_three_exact_audit :
    Complex.normSq ((1 / 3 : ℂ) + (tetraB : ℂ) * (starRingEnd ℂ) ω *
      ((tetraB : ℂ) * (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I))) =
      (1 / 3 : ℝ) := by
  change Complex.normSq ((1 / 3 : ℂ) + (tetraB : ℂ) * star ω *
    ((tetraB : ℂ) * (-(1 / 2 : ℂ) - ((Real.sqrt 3 : ℂ) / 2) * Complex.I))) =
    (1 / 3 : ℝ)
  exact overlap_two_three_audit

@[simp] private lemma overlap_three_one_audit :
    Complex.normSq ((1 / 3 : ℂ) + (tetraB : ℂ) *
      (-(1 : ℂ) / (starRingEnd ℂ) 2 +
        ((Real.sqrt 3 : ℂ) / (starRingEnd ℂ) 2) * Complex.I) * (tetraB : ℂ)) =
      (1 / 3 : ℝ) := by
  rw [explicit_omega_audit, tetraB_mul_mul_tetraB_audit]
  exact normSq_qubit_offdiag_omega_audit

@[simp] private lemma overlap_three_two_audit :
    Complex.normSq ((1 / 3 : ℂ) + (tetraB : ℂ) *
      (-(1 : ℂ) / (starRingEnd ℂ) 2 +
        ((Real.sqrt 3 : ℂ) / (starRingEnd ℂ) 2) * Complex.I) *
      ((tetraB : ℂ) * ω)) = (1 / 3 : ℝ) := by
  rw [explicit_omega_audit]
  ring_nf
  simpa only [pow_two, tetraB_sq_complex_audit] using
    normSq_qubit_offdiag_omega_sq_audit

@[simp] private lemma overlap_three_two_simplified_audit :
    Complex.normSq ((1 / 3 : ℂ) + (tetraB : ℂ) * ω *
      ((tetraB : ℂ) * ω)) = (1 / 3 : ℝ) := by
  have hphase :
      (tetraB : ℂ) * ω * ((tetraB : ℂ) * ω) = (2 / 3 : ℂ) * (ω ^ 2) := by
    calc
      (tetraB : ℂ) * ω * ((tetraB : ℂ) * ω) =
          ((tetraB : ℂ) * tetraB) * (ω ^ 2) := by ring
      _ = (2 / 3 : ℂ) * (ω ^ 2) := by rw [tetraB_sq_complex_audit]
  rw [hphase]
  exact normSq_qubit_offdiag_omega_sq_audit


@[simp] private lemma overlap_two_three_pow_audit :
    Complex.normSq ((1 / 3 : ℂ) + (tetraB : ℂ) * (starRingEnd ℂ) ω *
      ((tetraB : ℂ) * (ω ^ 2))) = (1 / 3 : ℝ) := by
  change Complex.normSq ((1 / 3 : ℂ) + (tetraB : ℂ) * star ω *
    ((tetraB : ℂ) * (ω ^ 2))) = (1 / 3 : ℝ)
  rw [star_omega_audit]
  have hphase :
      (tetraB : ℂ) * (ω ^ 2) * ((tetraB : ℂ) * (ω ^ 2)) =
        (2 / 3 : ℂ) * ω := by
    calc
      (tetraB : ℂ) * (ω ^ 2) * ((tetraB : ℂ) * (ω ^ 2)) =
((tetraB : ℂ) * tetraB) * ((ω ^ 2) * (ω ^ 2)) := by ring
      _ = (2 / 3 : ℂ) * ω := by
        rw [tetraB_sq_complex_audit, omega_sq_mul_omega_sq_audit]
  rw [hphase]
  exact normSq_qubit_offdiag_omega_audit

@[simp] private lemma normSq_qubit_offdiag_star_omega_pow_two_audit :
    Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) *
      ((starRingEnd ℂ) ω) ^ 2) = (1 / 3 : ℝ) := by
  change Complex.normSq ((1 / 3 : ℂ) + (2 / 3 : ℂ) * (star ω) ^ 2) =
    (1 / 3 : ℝ)
  rw [star_omega_audit]
  have hpow : (ω ^ 2) ^ 2 = ω := by
    calc
      (ω ^ 2) ^ 2 = ω ^ 4 := by ring
      _ = ω := omega_four_audit
  rw [hpow]
  exact normSq_qubit_offdiag_omega_audit

@[simp] private lemma overlap_three_two_star_pow_audit :
    Complex.normSq ((1 / 3 : ℂ) + (tetraB : ℂ) *
      ((starRingEnd ℂ) ω) ^ 2 * ((tetraB : ℂ) * ω)) = (1 / 3 : ℝ) := by
  change Complex.normSq ((1 / 3 : ℂ) + (tetraB : ℂ) *
    (star ω) ^ 2 * ((tetraB : ℂ) * ω)) = (1 / 3 : ℝ)
  rw [star_omega_audit]
  have hpow : (ω ^ 2) ^ 2 = ω := by
    calc
      (ω ^ 2) ^ 2 = ω ^ 4 := by ring
      _ = ω := omega_four_audit
  rw [hpow]
  exact overlap_three_two_simplified_audit

/-- The tetrahedral qubit SIC family has the correct constant pairwise overlap. -/
@[category test, AMS 15 47 81]
lemma qubitSICFamily_pairwise :
    HasConstantOverlapSq (sicOverlapSq 2) qubitSICFamily := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  interval_cases i <;> interval_cases j
  all_goals
    simp [qubitSICFamily, vec2, overlapSq, sicOverlapSq, Fin.sum_univ_two] at hij ⊢
    first
      | done
      | contradiction
      | norm_num [sicOverlapSq]

/-- Dimension $2$ admits a SIC-POVM, witnessed by the tetrahedral qubit SIC. -/
@[category test, AMS 15 47 81]
theorem hasSICPOVM_two : HasSICPOVM 2 := by
  refine ⟨qubitSICFamily, ?_⟩
  exact ⟨qubitSICFamily_normalized, qubitSICFamily_pairwise⟩

/-- Every vector in the Hesse qutrit SIC family is normalized. -/
@[category test, AMS 15 47 81]
lemma hesseFamily_normalized (i : Fin 9) :
    IsNormalized (hesseFamily i) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have sqrt2_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have omega2_norm : ‖ω ^ 2‖ = 1 := by rw [norm_pow, omega_norm]; ring
  fin_cases i <;>
    simp [IsNormalized, hesseFamily, vec3, mkStateVector,
      EuclideanSpace.norm_eq, Fin.sum_univ_three, hesseS,
      omega_norm, omega2_norm, abs_of_pos sqrt2_pos]
  all_goals (try (field_simp; linarith [h2]))

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

set_option linter.unnecessarySeqFocus false in
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

@[simp] private lemma q3_normSq_half_add_half_mul_star_omega_exact :
    Complex.normSq ((1 / 2 : ℂ) + (1 / 2 : ℂ) * (starRingEnd ℂ) ω) =
      (1 / 4 : ℝ) := by
  change Complex.normSq ((1 / 2 : ℂ) + (1 / 2 : ℂ) * star ω) = (1 / 4 : ℝ)
  rw [q3_star_omega]
  exact q3_normSq_half_add_half_mul_omega_sq

@[simp] private lemma q3_normSq_half_mul_star_omega_add_half_exact :
    Complex.normSq ((1 / 2 : ℂ) * (starRingEnd ℂ) ω + (1 / 2 : ℂ)) =
      (1 / 4 : ℝ) := by
  simpa [add_comm] using q3_normSq_half_add_half_mul_star_omega_exact

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


@[simp] private lemma q3_normSq_half_add_hesseS_star_omega_mul_hesseS_omega_sq :
    Complex.normSq ((1 / 2 : ℂ) + (hesseS : ℂ) * (starRingEnd ℂ) ω *
      ((hesseS : ℂ) * (ω ^ 2))) = (1 / 4 : ℝ) := by
  change Complex.normSq ((1 / 2 : ℂ) + (hesseS : ℂ) * star ω *
    ((hesseS : ℂ) * (ω ^ 2))) = (1 / 4 : ℝ)
  rw [q3_star_omega]
  have hphase :
      (hesseS : ℂ) * (ω ^ 2) * ((hesseS : ℂ) * (ω ^ 2)) =
        (1 / 2 : ℂ) * ω := by
    calc
      (hesseS : ℂ) * (ω ^ 2) * ((hesseS : ℂ) * (ω ^ 2)) =
((hesseS : ℂ) * hesseS) * ((ω ^ 2) * (ω ^ 2)) := by ring
      _ = (1 / 2 : ℂ) * ω := by
        rw [q3_hesseS_sq_complex, q3_omega_sq_mul_omega_sq]
  rw [hphase]
  exact q3_normSq_half_add_half_mul_omega

@[simp] private lemma q3_normSq_half_add_half_mul_star_omega_pow_two :
    Complex.normSq ((1 / 2 : ℂ) + (1 / 2 : ℂ) *
      ((starRingEnd ℂ) ω) ^ 2) = (1 / 4 : ℝ) := by
  change Complex.normSq ((1 / 2 : ℂ) + (1 / 2 : ℂ) * (star ω) ^ 2) =
    (1 / 4 : ℝ)
  rw [q3_star_omega]
  have hpow : (ω ^ 2) ^ 2 = ω := by
    calc
      (ω ^ 2) ^ 2 = ω ^ 4 := by ring
      _ = ω := q3_omega_four
  rw [hpow]
  exact q3_normSq_half_add_half_mul_omega

@[simp] private lemma q3_normSq_half_add_hesseS_star_omega_pow_two_mul_hesseS_omega :
    Complex.normSq ((1 / 2 : ℂ) + (hesseS : ℂ) *
      ((starRingEnd ℂ) ω) ^ 2 * ((hesseS : ℂ) * ω)) = (1 / 4 : ℝ) := by
  change Complex.normSq ((1 / 2 : ℂ) + (hesseS : ℂ) *
    (star ω) ^ 2 * ((hesseS : ℂ) * ω)) = (1 / 4 : ℝ)
  rw [q3_star_omega]
  have hpow : (ω ^ 2) ^ 2 = ω := by
    calc
      (ω ^ 2) ^ 2 = ω ^ 4 := by ring
      _ = ω := q3_omega_four
  rw [hpow]
  exact q3_normSq_half_add_hesseS_omega_mul_hesseS_omega

@[simp] private lemma q3_normSq_half_mul_omega_sq_add_half :
    Complex.normSq ((1 / 2 : ℂ) * (ω ^ 2) + (1 / 2 : ℂ)) =
      (1 / 4 : ℝ) := by
  simpa [add_comm] using q3_normSq_half_add_half_mul_omega_sq

@[simp] private lemma q3_normSq_hesseS_star_omega_mul_hesseS_omega_sq_add_half :
    Complex.normSq ((hesseS : ℂ) * (starRingEnd ℂ) ω *
      ((hesseS : ℂ) * (ω ^ 2)) + (1 / 2 : ℂ)) = (1 / 4 : ℝ) := by
  simpa [add_comm] using
    q3_normSq_half_add_hesseS_star_omega_mul_hesseS_omega_sq

@[simp] private lemma q3_normSq_half_mul_star_omega_pow_two_add_half :
    Complex.normSq ((1 / 2 : ℂ) * ((starRingEnd ℂ) ω) ^ 2 +
      (1 / 2 : ℂ)) = (1 / 4 : ℝ) := by
  simpa [add_comm] using q3_normSq_half_add_half_mul_star_omega_pow_two

@[simp] private lemma q3_normSq_hesseS_star_omega_pow_two_mul_hesseS_omega_add_half :
    Complex.normSq ((hesseS : ℂ) * ((starRingEnd ℂ) ω) ^ 2 *
      ((hesseS : ℂ) * ω) + (1 / 2 : ℂ)) = (1 / 4 : ℝ) := by
  simpa [add_comm] using
    q3_normSq_half_add_hesseS_star_omega_pow_two_mul_hesseS_omega

set_option maxHeartbeats 1000000 in
/-- The Hesse qutrit SIC family has the correct constant pairwise overlap. -/
@[category test, AMS 15 47 81]
lemma hesseFamily_pairwise :
    HasConstantOverlapSq (sicOverlapSq 3) hesseFamily := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  interval_cases i <;> interval_cases j
  all_goals
    simp [hesseFamily, vec3, overlapSq, sicOverlapSq, Fin.sum_univ_three] at hij ⊢
    first
      | done
      | contradiction
      | norm_num [sicOverlapSq]

/-- Dimension $3$ admits a SIC-POVM, witnessed by the Hesse qutrit SIC. -/
@[category test, AMS 15 47 81]
theorem hasSICPOVM_three : HasSICPOVM 3 := by
  refine ⟨hesseFamily, ?_⟩
  exact ⟨hesseFamily_normalized, hesseFamily_pairwise⟩

/-- Every vector in the BB84 family is normalized. -/
@[category test, AMS 15 47 81]
lemma bb84Family_normalized (i : Fin 4) :
    IsNormalized (bb84Family i) := by
  fin_cases i <;> simp [IsNormalized, bb84Family, vec2, EuclideanSpace.norm_eq, hesseS] <;> grind

/-- The BB84 family has the right cardinality for a qubit SIC but fails the constant-overlap condition. -/
@[category test, AMS 15 47 81]
theorem bb84Family_not_isSICFamily : ¬ IsSICFamily 2 bb84Family := by
  intro h
  have h_overlap := h.2 (show 0 ≠ 1 by decide)
  simp [Fin.sum_univ_two, bb84Family, vec2, overlapSq, sicOverlapSq_two] at h_overlap

/- ## Smallest open special cases (all d<=75) -/

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $56$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_56 : answer(sorry) ↔ HasSICPOVM 56 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $58$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_58 : answer(sorry) ↔ HasSICPOVM 58 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $59$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_59 : answer(sorry) ↔ HasSICPOVM 59 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $60$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_60 : answer(sorry) ↔ HasSICPOVM 60 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $64$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_64 : answer(sorry) ↔ HasSICPOVM 64 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $68$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_68 : answer(sorry) ↔ HasSICPOVM 68 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $69$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_69 : answer(sorry) ↔ HasSICPOVM 69 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $70$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_70 : answer(sorry) ↔ HasSICPOVM 70 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $71$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_71 : answer(sorry) ↔ HasSICPOVM 71 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $72$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_72 : answer(sorry) ↔ HasSICPOVM 72 := by sorry

/-- Benchmark open subproblem: existence of a SIC-POVM in dimension $75$. -/
@[category research open, AMS 15 47 81]
theorem hasSICPOVM_75 : answer(sorry) ↔ HasSICPOVM 75 := by sorry

/- ## Full conjecture -/

/-- Do SIC-POVMs exist in every finite dimension? -/
@[category research open, AMS 15 47 81]
theorem sicPOVMs :
    answer(sorry) ↔ ∀ d : ℕ, 1 ≤ d → HasSICPOVM d := by
  sorry

end OpenQuantumProblem23
