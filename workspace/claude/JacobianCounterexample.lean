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

import FormalConjectures.Wikipedia.JacobianConjecture

/-!
# A counterexample to the Jacobian conjecture (Alpöge, 2026)

This file **refutes** the `research open` statement
`JacobianConjecture.jacobian_conjecture` in
`FormalConjectures/Wikipedia/JacobianConjecture.lean`, by formalizing the
July 2026 counterexample of **Levent Alpöge** (announced 19 July 2026; the
problem was posed to him by Akhil Mathew, and the counterexample was found
with computer assistance).

Over `ℚ`, in the three variables `x = X 0`, `y = X 1`, `z = X 2`, consider the
polynomial map `F = (P, Q, R) : ℚ³ → ℚ³` given by

* `P = (1 + x*y)^3*z + y^2*(1 + x*y)*(4 + 3*x*y)`
* `Q = y + 3*x*(1 + x*y)^2*z + 3*x*y^2*(4 + 3*x*y)`
* `R = 2*x - 3*x^2*y - x^3*z`

Its Jacobian determinant is the nonzero constant `det J_F = -2`
(`jacobianDet_eq`, `isUnit_jacobianDet`), yet `F` is not injective: the three
distinct points `(0, 0, -1/4)`, `(1, -3/2, 13/2)` and `(-1, 3/2, 13/2)` all map
to `(-1/4, 0, 0)`.  Since a polynomial map with a polynomial left inverse is
injective, `F` admits no polynomial inverse (`not_injective_aeval`), and the
Jacobian conjecture is **false** in dimension 3 over `ℚ`
(`not_jacobian_conjecture`).  Adjoining identity coordinates extends the
counterexample to every dimension `≥ 3`; the two-dimensional case of the
Jacobian conjecture remains open.

Consequently the repository statement `JacobianConjecture.jacobian_conjecture`
— which quantifies over every field `k` of characteristic zero and every finite
index type `σ` — is FALSE as written: it should be retagged `research solved`,
with the answer being a refutation.

*References:*
* [Terence Tao, *A digestion of the Jacobian conjecture counterexample*](https://terrytao.wordpress.com/2026/07/21/a-digestion-of-the-jacobian-conjecture-counterexample/)
* [Secret Blogging Seminar, *The new counterexample to the Jacobian conjecture*](https://sbseminar.wordpress.com/2026/07/20/the-new-counterexample-to-the-jacobian-conjecture/)
-/

namespace JacobianCounterexample

open MvPolynomial JacobianConjecture JacobianConjecture.RegularFunction

local notation "xx" => (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ)
local notation "yy" => (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ)
local notation "zz" => (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℚ)

/-- First component of Alpöge's counterexample map:
`P = (1 + x*y)^3*z + y^2*(1 + x*y)*(4 + 3*x*y)`. -/
noncomputable def PP : MvPolynomial (Fin 3) ℚ :=
  (C 1 + xx * yy) ^ 3 * zz + yy ^ 2 * (C 1 + xx * yy) * (C 4 + C 3 * xx * yy)

/-- Second component of Alpöge's counterexample map:
`Q = y + 3*x*(1 + x*y)^2*z + 3*x*y^2*(4 + 3*x*y)`. -/
noncomputable def QQ : MvPolynomial (Fin 3) ℚ :=
  yy + C 3 * xx * (C 1 + xx * yy) ^ 2 * zz + C 3 * xx * yy ^ 2 * (C 4 + C 3 * xx * yy)

/-- Third component of Alpöge's counterexample map:
`R = 2*x - 3*x^2*y - x^3*z`. -/
noncomputable def RR : MvPolynomial (Fin 3) ℚ :=
  C 2 * xx - C 3 * xx ^ 2 * yy - xx ^ 3 * zz

/-- Alpöge's counterexample map `F = (P, Q, R) : ℚ³ → ℚ³`, as a
`RegularFunction`. -/
noncomputable def Fcex : RegularFunction ℚ (Fin 3) (Fin 3) := ![PP, QQ, RR]

section Partials

lemma pderiv_x_PP : pderiv (0 : Fin 3) PP =
    3 * xx ^ 2 * yy ^ 3 * zz + 6 * xx * yy ^ 4 + 6 * xx * yy ^ 2 * zz
      + 7 * yy ^ 3 + 3 * yy * zz := by
  unfold PP
  simp [pderiv_X]
  try simp only [map_ofNat]
  try ring

lemma pderiv_y_PP : pderiv (1 : Fin 3) PP =
    3 * xx ^ 3 * yy ^ 2 * zz + 12 * xx ^ 2 * yy ^ 3 + 6 * xx ^ 2 * yy * zz
      + 21 * xx * yy ^ 2 + 3 * xx * zz + 8 * yy := by
  unfold PP
  simp [pderiv_X]
  try simp only [map_ofNat]
  try ring

lemma pderiv_z_PP : pderiv (2 : Fin 3) PP =
    xx ^ 3 * yy ^ 3 + 3 * xx ^ 2 * yy ^ 2 + 3 * xx * yy + 1 := by
  unfold PP
  simp [pderiv_X]
  try simp only [map_ofNat]
  try ring

lemma pderiv_x_QQ : pderiv (0 : Fin 3) QQ =
    9 * xx ^ 2 * yy ^ 2 * zz + 18 * xx * yy ^ 3 + 12 * xx * yy * zz
      + 12 * yy ^ 2 + 3 * zz := by
  unfold QQ
  simp [pderiv_X]
  try simp only [map_ofNat]
  try ring

lemma pderiv_y_QQ : pderiv (1 : Fin 3) QQ =
    6 * xx ^ 3 * yy * zz + 27 * xx ^ 2 * yy ^ 2 + 6 * xx ^ 2 * zz
      + 24 * xx * yy + 1 := by
  unfold QQ
  simp [pderiv_X]
  try simp only [map_ofNat]
  try ring

lemma pderiv_z_QQ : pderiv (2 : Fin 3) QQ =
    3 * xx ^ 3 * yy ^ 2 + 6 * xx ^ 2 * yy + 3 * xx := by
  unfold QQ
  simp [pderiv_X]
  try simp only [map_ofNat]
  try ring

lemma pderiv_x_RR : pderiv (0 : Fin 3) RR =
    -3 * xx ^ 2 * zz - 6 * xx * yy + 2 := by
  unfold RR
  simp [pderiv_X]
  try simp only [map_ofNat]
  try ring

lemma pderiv_y_RR : pderiv (1 : Fin 3) RR = -3 * xx ^ 2 := by
  unfold RR
  simp [pderiv_X]
  try simp only [map_ofNat]
  try ring

lemma pderiv_z_RR : pderiv (2 : Fin 3) RR = -(xx ^ 3) := by
  unfold RR
  simp [pderiv_X]
  try simp only [map_ofNat]
  try ring

end Partials

/-- The Jacobian determinant of Alpöge's map is the constant `-2`. -/
theorem jacobianDet_eq : Fcex.Jacobian.det = -2 := by
  rw [Matrix.det_fin_three]
  simp only [RegularFunction.Jacobian, Matrix.of_apply, Fcex, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    pderiv_x_PP, pderiv_y_PP, pderiv_z_PP, pderiv_x_QQ, pderiv_y_QQ, pderiv_z_QQ,
    pderiv_x_RR, pderiv_y_RR, pderiv_z_RR]
  ring

/-- The Jacobian determinant of Alpöge's map is a unit. -/
theorem isUnit_jacobianDet : IsUnit Fcex.Jacobian.det := by
  rw [jacobianDet_eq]
  have hC : C (-2 : ℚ) = (-2 : MvPolynomial (Fin 3) ℚ) := by rw [map_neg, map_ofNat]
  rw [← hC]
  exact (isUnit_iff_ne_zero.mpr (by norm_num : (-2 : ℚ) ≠ 0)).map C

/-- The distinct points `(0, 0, -1/4)` and `(1, -3/2, 13/2)` have the same
image `(-1/4, 0, 0)` under Alpöge's map (in fact `(-1, 3/2, 13/2)` is a third
point with this image). -/
lemma aeval_collision :
    Fcex.aeval ![(0 : ℚ), 0, -1/4] = Fcex.aeval ![1, -3/2, 13/2] := by
  funext t
  fin_cases t <;>
    simp [RegularFunction.aeval, Fcex, PP, QQ, RR] <;>
    norm_num

/-- Alpöge's map is not injective as a map `ℚ³ → ℚ³`. -/
theorem not_injective_aeval :
    ¬ Function.Injective (Fcex.aeval : (Fin 3 → ℚ) → Fin 3 → ℚ) := by
  intro h
  have h0 := congrFun (h aeval_collision) 0
  norm_num [Matrix.cons_val_zero] at h0

/-- Evaluation of the identity regular function is the identity. -/
lemma id_aeval (a : Fin 3 → ℚ) :
    (RegularFunction.id ℚ (Fin 3)).aeval a = a := by
  funext t
  simp [RegularFunction.aeval, RegularFunction.id]

/-- The **Jacobian conjecture is false**: the repository statement
`JacobianConjecture.jacobian_conjecture`, specialized to `k = ℚ` and
`σ = Fin 3`, fails for Alpöge's counterexample map.  Since the repository
statement quantifies over all `k` and `σ`, it is refuted by this theorem. -/
theorem not_jacobian_conjecture :
    ¬ (∀ (F : JacobianConjecture.RegularFunction ℚ (Fin 3) (Fin 3)),
        IsUnit F.Jacobian.det →
        ∃ (G : JacobianConjecture.RegularFunction ℚ (Fin 3) (Fin 3)),
          G.comp F = JacobianConjecture.RegularFunction.id ℚ (Fin 3) ∧
          F.comp G = JacobianConjecture.RegularFunction.id ℚ (Fin 3)) := by
  intro h
  obtain ⟨G, -, hFG⟩ := h Fcex isUnit_jacobianDet
  refine not_injective_aeval fun a b hab => ?_
  have key : ∀ c : Fin 3 → ℚ, G.aeval (Fcex.aeval c) = c := fun c => by
    rw [← _root_.JacobianConjecture.comp_aeval, hFG, id_aeval]
  rw [← key a, hab, key b]

end JacobianCounterexample
