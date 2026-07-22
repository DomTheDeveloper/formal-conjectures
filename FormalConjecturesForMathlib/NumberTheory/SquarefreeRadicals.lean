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

import Mathlib.FieldTheory.PolynomialGaloisGroup
import FormalConjecturesForMathlib.LinearAlgebra.Eigencharacter
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Sqrt
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

open Finset Function Polynomial
open scoped BigOperators

noncomputable section

namespace SquarefreeRadicals

/-- The quadratic polynomial whose roots are `±√n`. -/
def quad (n : ℕ) : ℚ[X] := X ^ 2 - C (n : ℚ)

/-- A product of the quadratic polynomials attached to a finite set. -/
def quadProduct (S : Finset ℕ) : ℚ[X] := ∏ n ∈ S, quad n

lemma quad_monic (n : ℕ) : (quad n).Monic := by
  simpa [quad] using monic_X_pow_sub_C (n : ℚ) (by decide : (2 : ℕ) ≠ 0)

lemma quad_ne_zero (n : ℕ) : quad n ≠ 0 := (quad_monic n).ne_zero

lemma quadProduct_monic (S : Finset ℕ) : (quadProduct S).Monic := by
  apply monic_prod_of_monic
  intro n hn
  exact quad_monic n

lemma quadProduct_ne_zero (S : Finset ℕ) : quadProduct S ≠ 0 := (quadProduct_monic S).ne_zero

lemma quad_isCoprime {m n : ℕ} (h : m ≠ n) : IsCoprime (quad m) (quad n) := by
  let d : ℚ := (n : ℚ) - m
  have hd : d ≠ 0 := by
    dsimp [d]
    exact sub_ne_zero.mpr (by exact_mod_cast h.symm)
  refine ⟨C d⁻¹, -C d⁻¹, ?_⟩
  dsimp [quad, d]
  field_simp [hd]
  ring

lemma quad_separable {n : ℕ} (hn : n ≠ 0) : (quad n).Separable := by
  let u : ℚˣ := Units.mk0 (n : ℚ) (by exact_mod_cast hn)
  have htwo : IsUnit (2 : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
  simpa [quad, u] using separable_X_pow_sub_C_unit u htwo

lemma quadProduct_separable (S : Finset ℕ) (hpos : ∀ n ∈ S, n ≠ 0) :
    (quadProduct S).Separable := by
  apply separable_prod'
  · intro m hm n hn hmn
    exact quad_isCoprime hmn
  · intro n hn
    exact quad_separable (hpos n hn)

lemma quad_dvd_quadProduct {S : Finset ℕ} {n : ℕ} (hn : n ∈ S) :
    quad n ∣ quadProduct S := by
  exact Finset.dvd_prod_of_mem (fun n => quad n) hn

/-- The common splitting field of all quadratic polynomials in `S`. -/
abbrev RadicalField (S : Finset ℕ) := (quadProduct S).SplittingField

/-- Each quadratic factor splits in the common splitting field. -/
lemma quad_splits (S : Finset ℕ) (n : S) :
    ((quad n.1).map (algebraMap ℚ (RadicalField S))).Splits := by
  have hP : ((quadProduct S).map (algebraMap ℚ (RadicalField S))).Splits :=
    Polynomial.SplittingField.splits (quadProduct S)
  apply hP.of_dvd
  · exact map_ne_zero (quadProduct_ne_zero S)
  · rcases quad_dvd_quadProduct n.2 with ⟨r, hr⟩
    refine ⟨r.map (algebraMap ℚ (RadicalField S)), ?_⟩
    rw [← map_mul, hr]

lemma quad_mapped_degree_ne_zero (S : Finset ℕ) (n : S) :
    ((quad n.1).map (algebraMap ℚ (RadicalField S))).degree ≠ 0 := by
  rw [(quad_monic n.1).degree_map]
  simp [quad]

/-- A chosen square root of each radicand inside the common splitting field. -/
def root (S : Finset ℕ) (n : S) : RadicalField S :=
  Polynomial.rootOfSplits (quad_splits S n) (quad_mapped_degree_ne_zero S n)

lemma root_spec (S : Finset ℕ) (n : S) :
    root S n ^ 2 = algebraMap ℚ (RadicalField S) (n.1 : ℚ) := by
  have h := Polynomial.eval_rootOfSplits (quad_splits S n) (quad_mapped_degree_ne_zero S n)
  simpa [root, quad] using h

lemma root_ne_zero (S : Finset ℕ) (n : S) (hn : n.1 ≠ 0) : root S n ≠ 0 := by
  intro h
  have hs := root_spec S n
  rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
  exact (map_ne_zero (by exact_mod_cast hn)) hs.symm

/-- Every Galois automorphism sends a chosen square root to itself or its negative. -/
lemma gal_root_eq_or_neg (S : Finset ℕ) (n : S)
    (σ : (quadProduct S).Gal) :
    σ (root S n) = root S n ∨ σ (root S n) = -root S n := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [map_pow, root_spec, root_spec]
  simp

/-- A rational square which is a natural number is already a natural square. -/
lemma exists_nat_mul_self_of_exists_rat_mul_self {N : ℕ}
    (h : ∃ q : ℚ, q * q = (N : ℚ)) :
    ∃ u : ℕ, u * u = N := by
  have hsqrt : Rat.sqrt (N : ℚ) * Rat.sqrt (N : ℚ) = (N : ℚ) :=
    (Rat.exists_mul_self (N : ℚ)).mp h
  rw [Rat.sqrt_natCast] at hsqrt
  exact ⟨Nat.sqrt N, by exact_mod_cast hsqrt⟩

/-- Two nonzero squarefree naturals whose product is a rational square are equal. -/
lemma squarefree_eq_of_mul_is_rat_square {m n : ℕ}
    (hm0 : m ≠ 0) (hn0 : n ≠ 0) (hm : Squarefree m) (hn : Squarefree n)
    (h : ∃ q : ℚ, q * q = (m * n : ℕ)) :
    m = n := by
  obtain ⟨u, hu⟩ := exists_nat_mul_self_of_exists_rat_mul_self h
  have hdvd (a b : ℕ) (ha : Squarefree a)
      (hub : u * u = a * b) : a ∣ b := by
    have ha_u_sq : a ∣ u ^ 2 := by
      rw [pow_two, hub]
      exact dvd_mul_right a b
    have ha_u : a ∣ u := (ha.dvd_pow_iff_dvd (by decide : (2 : ℕ) ≠ 0)).mp ha_u_sq
    obtain ⟨c, rfl⟩ := ha_u
    have hac : a * (c * c) = b := by
      apply Nat.mul_left_cancel
      calc
        a * (a * (c * c)) = (a * c) * (a * c) := by ring
        _ = a * b := hub
    exact ⟨c * c, hac.symm⟩
  exact Nat.dvd_antisymm
    (hdvd m n hm hu)
    (hdvd n m hn (by simpa [mul_comm] using hu))

/-- The sign character through which the Galois group acts on a chosen radical. -/
noncomputable def radicalChar (S : Finset ℕ) (n : S) (hn : n.1 ≠ 0) :
    (quadProduct S).Gal →* ℚ := by
  let hv : root S n ≠ 0 := root_ne_zero S n hn
  let horbit : ∀ σ : (quadProduct S).Gal,
      σ • root S n = root S n ∨ σ • root S n = -root S n := by
    intro σ
    simpa only [AlgEquiv.smul_def] using gal_root_eq_or_neg S n σ
  exact Eigencharacter.signHom (K := ℚ) (root S n) hv horbit

lemma radicalChar_eigen (S : Finset ℕ) (n : S) (hn : n.1 ≠ 0)
    (σ : (quadProduct S).Gal) :
    σ • root S n =
      algebraMap ℚ (RadicalField S) (radicalChar S n hn σ) * root S n := by
  simp only [radicalChar]
  exact Eigencharacter.signHom_eigen (K := ℚ) σ

/-- Distinct nonzero squarefree radicands give distinct Galois sign characters. -/
lemma radicalChar_injective (S : Finset ℕ)
    (hpos : ∀ n ∈ S, n ≠ 0) (hsq : ∀ n ∈ S, Squarefree n) :
    Injective (fun n : S => radicalChar S n (hpos n.1 n.2)) := by
  letI : IsGalois ℚ (RadicalField S) :=
    IsGalois.of_separable_splitting_field (quadProduct_separable S hpos)
  intro m n hχ
  apply Subtype.ext
  have hm0 : m.1 ≠ 0 := hpos m.1 m.2
  have hn0 : n.1 ≠ 0 := hpos n.1 n.2
  let hm_orbit : ∀ τ : (quadProduct S).Gal,
      τ • root S m = root S m ∨ τ • root S m = -root S m := by
    intro τ
    simpa only [AlgEquiv.smul_def] using gal_root_eq_or_neg S m τ
  let hn_orbit : ∀ τ : (quadProduct S).Gal,
      τ • root S n = root S n ∨ τ • root S n = -root S n := by
    intro τ
    simpa only [AlgEquiv.smul_def] using gal_root_eq_or_neg S n τ
  have hχ' :
      Eigencharacter.signHom (K := ℚ) (root S m) (root_ne_zero S m hm0) hm_orbit =
        Eigencharacter.signHom (K := ℚ) (root S n) (root_ne_zero S n hn0) hn_orbit := by
    simpa [radicalChar] using hχ
  have hfixed : ∀ σ : (quadProduct S).Gal,
      σ (root S m * root S n) = root S m * root S n := by
    intro σ
    have hmul := Eigencharacter.fixed_mul_of_signHom_eq
      (K := ℚ) (E := RadicalField S) (G := (quadProduct S).Gal)
      (v := root S m) (w := root S n)
      (hv := root_ne_zero S m hm0) (hw := root_ne_zero S n hn0)
      (hv_orbit := hm_orbit) (hw_orbit := hn_orbit) hχ' σ
    simpa only [AlgEquiv.smul_def] using hmul
  have hrange : root S m * root S n ∈ Set.range (algebraMap ℚ (RadicalField S)) :=
    (IsGalois.mem_range_algebraMap_iff_fixed (root S m * root S n)).2 hfixed
  obtain ⟨q, hq⟩ := hrange
  have hq_sq : q * q = ((m.1 * n.1 : ℕ) : ℚ) := by
    apply (algebraMap ℚ (RadicalField S)).injective
    calc
      algebraMap ℚ (RadicalField S) (q * q)
          = (root S m * root S n) * (root S m * root S n) := by rw [map_mul, hq, hq]
      _ = (root S m) ^ 2 * (root S n) ^ 2 := by ring
      _ = algebraMap ℚ (RadicalField S) (m.1 : ℚ) *
          algebraMap ℚ (RadicalField S) (n.1 : ℚ) := by rw [root_spec, root_spec]
      _ = algebraMap ℚ (RadicalField S) (((m.1 * n.1 : ℕ) : ℚ)) := by norm_num
  exact squarefree_eq_of_mul_is_rat_square hm0 hn0 (hsq m.1 m.2) (hsq n.1 n.2)
    ⟨q, hq_sq⟩

/-- The chosen radicals attached to a finite family of distinct nonzero squarefree naturals
are linearly independent over the rationals. -/
theorem root_linearIndependent (S : Finset ℕ)
    (hpos : ∀ n ∈ S, n ≠ 0) (hsq : ∀ n ∈ S, Squarefree n) :
    LinearIndependent ℚ (root S) := by
  apply Eigencharacter.linearIndependent_of_eigencharacters
    (K := ℚ) (E := RadicalField S) (G := (quadProduct S).Gal)
    (v := root S)
  · intro n
    exact root_ne_zero S n (hpos n.1 n.2)
  · exact fun n => radicalChar S n (hpos n.1 n.2)
  · exact radicalChar_injective S hpos hsq
  · intro n σ
    exact radicalChar_eigen S n (hpos n.1 n.2) σ

end SquarefreeRadicals
