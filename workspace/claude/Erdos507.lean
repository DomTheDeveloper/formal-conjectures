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

import FormalConjectures.ErdosProblems.«507»

/-!
# Erdős Problem 507 is degenerately formalized: `Erdos507.α` is identically zero

The formalization of the Heilbronn triangle problem in
`FormalConjectures/ErdosProblems/507.lean` uses the *signed* triangle area
`EuclideanGeometry.triangle_area a b c = positiveOrientation.areaForm (a -ᵥ c) (b -ᵥ c) / 2`
(defined in `FormalConjecturesForMathlib/Geometry/2d.lean`), and
`Erdos507.minTriangleArea S` takes an `sInf` over *all* vertex orderings of triangles with
vertices in `S`.  Swapping two vertices of a triangle negates the signed area, so every
admissible (non-collinear) configuration `S` contains triangles of both signs of area, and
`minTriangleArea S ≤ 0`.  Hence `Erdos507.α n ≤ 0`.  Conversely, arbitrarily "flat"
configurations of `n` points in the unit disk have all their (signed) triangle areas
arbitrarily close to `0`, so `Erdos507.α n ≥ 0`.  (For `n < 3` the admissible family is
empty and `Real.sSup ∅ = 0`.)  Therefore `Erdos507.α n = 0` for every `n`.

Consequences proved in this file:

* `alpha_eq_zero` : `∀ n, Erdos507.α n = 0`.
* `erdos_507_upper_answered` : the statement shape of `erdos_507.upper` is satisfied by
  the zero function, so the formalized "upper bound" problem is trivially answerable.
* `erdos_507_lower_unanswerable` : *no* answer can make the statement of
  `erdos_507.lower` true, since `Erdos507.lowerBest` is eventually positive.
* `not_lower_erdos`, `not_lower_kps82` : the two lower-bound variants tagged
  `research solved` in the source file (`erdos_507.variants.lower_erdos` and
  `erdos_507.variants.lower_kps82`) are in fact *false* as stated.

None of this reflects on the actual Heilbronn triangle problem; it shows only that the
formal statements in `507.lean` do not capture it (the area should be unsigned, e.g.
`|triangle_area|`).
-/

open Asymptotics Filter EuclideanGeometry
open scoped EuclideanGeometry

/- ### The set of signed triangle areas of a configuration -/

/-- The set over which `Erdos507.minTriangleArea S` takes its infimum. -/
private def areaSet (S : Finset ℝ²) : Set ℝ :=
  {EuclideanGeometry.triangle_area (t.points 0) (t.points 1) (t.points 2) |
    (t : Affine.Triangle ℝ ℝ²) (_ : ∀ i, t.points i ∈ S)}

private lemma minTriangleArea_eq (S : Finset ℝ²) :
    Erdos507.minTriangleArea S = sInf (areaSet S) := rfl

private lemma mem_areaSet_iff {S : Finset ℝ²} {x : ℝ} :
    x ∈ areaSet S ↔ ∃ (t : Affine.Triangle ℝ ℝ²) (_ : ∀ i, t.points i ∈ S),
      triangle_area (t.points 0) (t.points 1) (t.points 2) = x := Iff.rfl

/-- The family of point configurations over which `Erdos507.α n` takes its supremum. -/
private def family (n : ℕ) : Set (Finset ℝ²) :=
  { S : Finset ℝ² |
    S.card = n ∧ ↑S ⊆ Metric.closedBall (0 : ℝ²) 1 ∧ ¬ Collinear ℝ (S : Set ℝ²) }

private lemma alpha_eq (n : ℕ) :
    Erdos507.α n = sSup (Erdos507.minTriangleArea '' family n) := rfl

private lemma mem_family_iff {n : ℕ} {S : Finset ℝ²} :
    S ∈ family n ↔
      S.card = n ∧ ↑S ⊆ Metric.closedBall (0 : ℝ²) 1 ∧ ¬ Collinear ℝ (S : Set ℝ²) :=
  Iff.rfl

/-- The value set of `minTriangleArea` is finite (hence bounded below). -/
private lemma areaSet_finite (S : Finset ℝ²) : (areaSet S).Finite := by
  apply Set.Finite.subset ((Set.Finite.pi fun _ : Fin 3 => S.finite_toSet).image
    fun v : Fin 3 → ℝ² => triangle_area (v 0) (v 1) (v 2))
  intro x hx
  obtain ⟨t, ht, rfl⟩ := mem_areaSet_iff.mp hx
  exact ⟨t.points, Set.mem_univ_pi.mpr fun i => ht i, rfl⟩

private lemma triangle_mem_areaSet {S : Finset ℝ²} {a b c : ℝ²} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (h : AffineIndependent ℝ ![a, b, c]) :
    triangle_area a b c ∈ areaSet S := by
  refine mem_areaSet_iff.mpr ⟨⟨![a, b, c], h⟩, fun i => ?_, rfl⟩
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

/-- The signed area is antisymmetric in the first two vertices. -/
private lemma triangle_area_swap (a b c : ℝ²) :
    triangle_area b a c = - triangle_area a b c := by
  show positiveOrientation.areaForm (b -ᵥ c) (a -ᵥ c) / 2 =
    -(positiveOrientation.areaForm (a -ᵥ c) (b -ᵥ c) / 2)
  rw [Orientation.areaForm_swap]
  ring

/- ### A non-collinear set contains a non-collinear triple -/

private lemma collinear_of_forall_triple {s : Set ℝ²}
    (H : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, Collinear ℝ ({a, b, c} : Set ℝ²)) :
    Collinear ℝ s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact collinear_empty ℝ ℝ²
  by_cases hall : ∀ q ∈ s, q = p₀
  · exact Collinear.subset (fun q hq => hall q hq) (collinear_singleton ℝ p₀)
  push_neg at hall
  obtain ⟨p₁, hp₁, hp₁ne⟩ := hall
  rw [collinear_iff_of_mem hp₀]
  refine ⟨p₁ -ᵥ p₀, fun q hq => ?_⟩
  obtain ⟨w, hw⟩ := (collinear_iff_of_mem
    (show p₀ ∈ ({p₀, p₁, q} : Set ℝ²) by simp)).mp (H p₀ hp₀ p₁ hp₁ q hq)
  obtain ⟨r₁, hr₁⟩ := hw p₁ (by simp)
  obtain ⟨rq, hrq⟩ := hw q (by simp)
  have hr₁ne : r₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_vadd] at hr₁
    exact hp₁ne hr₁
  refine ⟨rq / r₁, ?_⟩
  have hv : p₁ -ᵥ p₀ = r₁ • w := by rw [hr₁, vadd_vsub]
  rw [hrq, hv, smul_smul, div_mul_cancel₀ _ hr₁ne]

private lemma exists_not_collinear_triple {s : Set ℝ²} (h : ¬ Collinear ℝ s) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ¬ Collinear ℝ ({a, b, c} : Set ℝ²) := by
  by_contra hcon
  push_neg at hcon
  exact h (collinear_of_forall_triple hcon)

/- ### Part A: `minTriangleArea S ≤ 0` for every admissible `S`, so `α n ≤ 0` -/

private lemma minTriangleArea_nonpos {S : Finset ℝ²} (hS : ¬ Collinear ℝ (S : Set ℝ²)) :
    Erdos507.minTriangleArea S ≤ 0 := by
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := exists_not_collinear_triple hS
  have habc' : ¬ Collinear ℝ ({b, a, c} : Set ℝ²) := by
    rw [Set.insert_comm]
    exact habc
  have h1 : AffineIndependent ℝ ![a, b, c] := affineIndependent_iff_not_collinear_set.mpr habc
  have h2 : AffineIndependent ℝ ![b, a, c] := affineIndependent_iff_not_collinear_set.mpr habc'
  have hbdd : BddBelow (areaSet S) := (areaSet_finite S).bddBelow
  have i1 := csInf_le hbdd (triangle_mem_areaSet ha hb hc h1)
  have i2 := csInf_le hbdd (triangle_mem_areaSet hb ha hc h2)
  rw [triangle_area_swap] at i2
  rw [minTriangleArea_eq]
  linarith

private lemma alpha_nonpos (n : ℕ) : Erdos507.α n ≤ 0 := by
  rw [alpha_eq]
  apply Real.sSup_nonpos
  rintro x ⟨S, hS, rfl⟩
  exact minTriangleArea_nonpos (mem_family_iff.mp hS).2.2

private lemma bddAbove_image (n : ℕ) : BddAbove (Erdos507.minTriangleArea '' family n) := by
  refine ⟨0, ?_⟩
  rintro x ⟨S, hS, rfl⟩
  exact minTriangleArea_nonpos (mem_family_iff.mp hS).2.2

/- ### Part B: flat configurations, `α n ≥ 0` -/

/-- `n` points in the unit disk: `!₂[0, δ]` together with `!₂[0, 0], !₂[δ, 0], !₂[2δ, 0], …`
on the `x`-axis.  For small `δ > 0` every triangle they span has tiny (signed) area. -/
private noncomputable def pts (δ : ℝ) (i : ℕ) : ℝ² :=
  if i = 0 then !₂[0, δ] else !₂[((i - 1 : ℕ) : ℝ) * δ, 0]

private lemma app₀ (x y : ℝ) : (!₂[x, y]) 0 = x := rfl

private lemma app₁ (x y : ℝ) : (!₂[x, y]) 1 = y := rfl

private lemma pts_zero (δ : ℝ) : pts δ 0 = !₂[0, δ] := by simp [pts]

private lemma pts_succ (δ : ℝ) (i : ℕ) : pts δ (i + 1) = !₂[(i : ℝ) * δ, 0] := by
  simp [pts]

private lemma pts_one (δ : ℝ) : pts δ 1 = !₂[0, 0] := by
  norm_num [pts]

private lemma pts_two (δ : ℝ) : pts δ 2 = !₂[δ, 0] := by
  norm_num [pts]

private lemma pts_injective {δ : ℝ} (hδ : 0 < δ) : Function.Injective (pts δ) := by
  intro a b hab
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | succ j =>
      exfalso
      have h := congrArg (fun p : ℝ² => p 1) hab
      simp only [pts_zero, pts_succ, app₁] at h
      exact hδ.ne' h
  | succ i =>
    cases b with
    | zero =>
      exfalso
      have h := congrArg (fun p : ℝ² => p 1) hab
      simp only [pts_zero, pts_succ, app₁] at h
      exact hδ.ne h
    | succ j =>
      have h := congrArg (fun p : ℝ² => p 0) hab
      simp only [pts_succ, app₀] at h
      have h2 : (i : ℝ) = (j : ℝ) := mul_right_cancel₀ hδ.ne' h
      have h3 : i = j := Nat.cast_injective h2
      omega

private lemma pts_coord_bounds {δ : ℝ} (hδ : 0 ≤ δ) {n : ℕ} {p : ℝ²}
    (hp : p ∈ (Finset.range n).image (pts δ)) :
    0 ≤ p 0 ∧ p 0 ≤ (n : ℝ) * δ ∧ 0 ≤ p 1 ∧ p 1 ≤ δ := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  have hin : i < n := Finset.mem_range.mp hi
  cases i with
  | zero =>
    rw [pts_zero, app₀, app₁]
    exact ⟨le_refl 0, mul_nonneg (Nat.cast_nonneg n) hδ, hδ, le_refl δ⟩
  | succ j =>
    rw [pts_succ, app₀, app₁]
    have hj : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : j ≤ n)
    exact ⟨mul_nonneg (Nat.cast_nonneg j) hδ, mul_le_mul_of_nonneg_right hj hδ,
      le_refl 0, hδ⟩

private lemma pts_mem_ball {δ : ℝ} {n : ℕ} (hδ : 0 ≤ δ) (hnδ : (n : ℝ) * δ ≤ 1 / 4)
    (hδ4 : δ ≤ 1 / 4) :
    ↑((Finset.range n).image (pts δ)) ⊆ Metric.closedBall (0 : ℝ²) 1 := by
  intro p hp
  obtain ⟨h0, h1, h2, h3⟩ := pts_coord_bounds hδ (Finset.mem_coe.mp hp)
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg h2]
  refine Real.sqrt_le_one.mpr ?_
  have h4 : p 0 ≤ 1 / 4 := h1.trans hnδ
  have h5 : p 1 ≤ 1 / 4 := h3.trans hδ4
  nlinarith

private lemma not_collinear_pts_triple {δ : ℝ} (hδ : 0 < δ) :
    ¬ Collinear ℝ ({pts δ 0, pts δ 1, pts δ 2} : Set ℝ²) := by
  intro hcol
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp hcol
  obtain ⟨ra, hA⟩ := hv (pts δ 0) (by simp)
  obtain ⟨rb, hB⟩ := hv (pts δ 1) (by simp)
  obtain ⟨rc, hC⟩ := hv (pts δ 2) (by simp)
  have comp : ∀ (p : ℝ²) (r : ℝ), p = r • v +ᵥ p₀ → ∀ i : Fin 2, p i = r * v i + p₀ i := by
    intro p r h i
    rw [h]
    rfl
  have eA1 : δ = ra * v 1 + p₀ 1 := by
    have h := comp _ _ hA 1
    rwa [pts_zero, app₁] at h
  have eB0 : (0 : ℝ) = rb * v 0 + p₀ 0 := by
    have h := comp _ _ hB 0
    rwa [pts_one, app₀] at h
  have eB1 : (0 : ℝ) = rb * v 1 + p₀ 1 := by
    have h := comp _ _ hB 1
    rwa [pts_one, app₁] at h
  have eC0 : δ = rc * v 0 + p₀ 0 := by
    have h := comp _ _ hC 0
    rwa [pts_two, app₀] at h
  have eC1 : (0 : ℝ) = rc * v 1 + p₀ 1 := by
    have h := comp _ _ hC 1
    rwa [pts_two, app₁] at h
  have eA0 : (0 : ℝ) = ra * v 0 + p₀ 0 := by
    have h := comp _ _ hA 0
    rwa [pts_zero, app₀] at h
  have d1 : (ra - rb) * v 0 = 0 := by linear_combination eB0 - eA0
  have d2 : (ra - rb) * v 1 = δ := by linear_combination eB1 - eA1
  have d3 : (rc - rb) * v 0 = δ := by linear_combination eB0 - eC0
  have d4 : (rc - rb) * v 1 = 0 := by linear_combination eB1 - eC1
  have hzero : δ * δ = 0 := by
    calc δ * δ = ((ra - rb) * v 1) * ((rc - rb) * v 0) := by rw [d2, d3]
      _ = ((ra - rb) * v 0) * ((rc - rb) * v 1) := by ring
      _ = 0 * 0 := by rw [d1, d4]
      _ = 0 := by ring
  exact (mul_pos hδ hδ).ne' hzero

private lemma pts_affineIndependent {δ : ℝ} (hδ : 0 < δ) :
    AffineIndependent ℝ ![pts δ 0, pts δ 1, pts δ 2] :=
  affineIndependent_iff_not_collinear_set.mpr (not_collinear_pts_triple hδ)

private lemma not_collinear_pts {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 3 ≤ n) :
    ¬ Collinear ℝ (((Finset.range n).image (pts δ) : Finset ℝ²) : Set ℝ²) := by
  intro hcol
  apply not_collinear_pts_triple hδ
  refine Collinear.subset ?_ hcol
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl <;>
    exact Finset.mem_coe.mpr
      (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)))

/-- Every triangle with vertices among the `pts δ` configuration has signed area at least
`-(3/2 · (nδ)δ)`. -/
private lemma area_lower_bound {N δ : ℝ} {a b c : ℝ²}
    (ha : 0 ≤ a 0 ∧ a 0 ≤ N ∧ 0 ≤ a 1 ∧ a 1 ≤ δ)
    (hb : 0 ≤ b 0 ∧ b 0 ≤ N ∧ 0 ≤ b 1 ∧ b 1 ≤ δ)
    (hc : 0 ≤ c 0 ∧ c 0 ≤ N ∧ 0 ≤ c 1 ∧ c 1 ≤ δ) :
    -(3 / 2 * (N * δ)) ≤ triangle_area a b c := by
  obtain ⟨ha0, ha1, ha2, ha3⟩ := ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := hc
  have hN : 0 ≤ N := ha0.trans ha1
  have harea : triangle_area a b c =
      (a 0 * b 1 - a 0 * c 1 - b 0 * a 1 + b 0 * c 1 + c 0 * a 1 - c 0 * b 1) / 2 := by
    rw [triangle_area_eq_det, Matrix.det_fin_three]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_fin_const, Matrix.of_apply,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  rw [harea]
  have h1 : a 0 * c 1 ≤ N * δ := mul_le_mul ha1 hc3 hc2 hN
  have h2 : b 0 * a 1 ≤ N * δ := mul_le_mul hb1 ha3 ha2 hN
  have h3 : c 0 * b 1 ≤ N * δ := mul_le_mul hc1 hb3 hb2 hN
  have h4 : 0 ≤ a 0 * b 1 := mul_nonneg ha0 hb2
  have h5 : 0 ≤ b 0 * c 1 := mul_nonneg hb0 hc2
  have h6 : 0 ≤ c 0 * a 1 := mul_nonneg hc0 ha2
  linarith

private lemma minTriangleArea_pts_ge {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 3 ≤ n) :
    -(3 / 2 * (((n : ℝ) * δ) * δ)) ≤
      Erdos507.minTriangleArea ((Finset.range n).image (pts δ)) := by
  rw [minTriangleArea_eq]
  have hmem : ∀ k : ℕ, k < n → pts δ k ∈ (Finset.range n).image (pts δ) := fun k hk =>
    Finset.mem_image_of_mem _ (Finset.mem_range.mpr hk)
  refine le_csInf ⟨_, triangle_mem_areaSet (hmem 0 (by omega)) (hmem 1 (by omega))
    (hmem 2 (by omega)) (pts_affineIndependent hδ)⟩ ?_
  rintro x hx
  obtain ⟨t, ht, rfl⟩ := mem_areaSet_iff.mp hx
  exact area_lower_bound (pts_coord_bounds hδ.le (ht 0)) (pts_coord_bounds hδ.le (ht 1))
    (pts_coord_bounds hδ.le (ht 2))

private lemma neg_le_alpha {n : ℕ} (hn : 3 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    -ε ≤ Erdos507.α n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  set δ : ℝ := min (1 / (4 * ((n : ℝ) + 1))) (Real.sqrt (ε / (2 * n))) with hδdef
  have hδpos : 0 < δ :=
    lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))
  have hδa : δ ≤ 1 / (4 * ((n : ℝ) + 1)) := min_le_left _ _
  -- `n·δ ≤ 1/4`
  have hkey : ((n : ℝ) + 1) * (1 / (4 * ((n : ℝ) + 1))) = 1 / 4 := by
    field_simp
  have hnδ : (n : ℝ) * δ ≤ 1 / 4 := by
    calc (n : ℝ) * δ ≤ ((n : ℝ) + 1) * δ :=
          mul_le_mul_of_nonneg_right (by linarith) hδpos.le
      _ ≤ ((n : ℝ) + 1) * (1 / (4 * ((n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hδa (by positivity)
      _ = 1 / 4 := hkey
  have hδ4 : δ ≤ 1 / 4 := by
    refine hδa.trans ?_
    calc 1 / (4 * ((n : ℝ) + 1)) ≤ ((n : ℝ) + 1) * (1 / (4 * ((n : ℝ) + 1))) := by
          nlinarith [one_div_pos.mpr (show (0:ℝ) < 4 * ((n : ℝ) + 1) by positivity)]
      _ = 1 / 4 := hkey
  -- `2nδ² ≤ ε`
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ ε / (2 * n) by positivity)
  have hδb : δ ≤ Real.sqrt (ε / (2 * n)) := min_le_right _ _
  have hδsq : δ ^ 2 ≤ ε / (2 * n) := by
    nlinarith [Real.sqrt_nonneg (ε / (2 * n))]
  have h2nδ : 2 * (n : ℝ) * δ ^ 2 ≤ ε := by
    have hmul : 2 * (n : ℝ) * δ ^ 2 ≤ 2 * (n : ℝ) * (ε / (2 * n)) :=
      mul_le_mul_of_nonneg_left hδsq (by positivity)
    have heq : 2 * (n : ℝ) * (ε / (2 * n)) = ε := by
      field_simp
    linarith
  -- the configuration
  have hcard : ((Finset.range n).image (pts δ)).card = n := by
    rw [Finset.card_image_of_injective _ (pts_injective hδpos), Finset.card_range]
  have hfam : (Finset.range n).image (pts δ) ∈ family n :=
    mem_family_iff.mpr ⟨hcard, pts_mem_ball hδpos.le hnδ hδ4, not_collinear_pts hδpos hn⟩
  have hmta := minTriangleArea_pts_ge hδpos hn
  calc -ε ≤ -(3 / 2 * (((n : ℝ) * δ) * δ)) := by nlinarith
    _ ≤ Erdos507.minTriangleArea ((Finset.range n).image (pts δ)) := hmta
    _ ≤ Erdos507.α n := by
        rw [alpha_eq]
        exact le_csSup (bddAbove_image n) (Set.mem_image_of_mem _ hfam)

/- ### Small cardinalities: the family is empty -/

private lemma collinear_of_card_le_two {S : Finset ℝ²} (h : S.card ≤ 2) :
    Collinear ℝ (S : Set ℝ²) := by
  obtain h0 | h1 | h2 : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  · rw [Finset.card_eq_zero.mp h0]
    simp only [Finset.coe_empty]
    exact collinear_empty ℝ ℝ²
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    simp only [Finset.coe_singleton]
    exact collinear_singleton ℝ a
  · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h2
    simp only [Finset.coe_insert, Finset.coe_singleton]
    exact collinear_pair ℝ a b

/- ### Main theorem -/

/-- The quantity `α` of the formalization of Erdős Problem 507 is identically zero:
the `sInf` in `minTriangleArea` ranges over signed areas of all vertex orderings. -/
theorem alpha_eq_zero : ∀ n, Erdos507.α n = 0 := by
  intro n
  rcases lt_or_ge n 3 with hn | hn
  · -- for `n < 3` the family is empty
    have hempty : Erdos507.minTriangleArea '' family n = ∅ := by
      rw [Set.image_eq_empty, Set.eq_empty_iff_forall_notMem]
      rintro S hS
      obtain ⟨hcard, -, hncol⟩ := mem_family_iff.mp hS
      exact hncol (collinear_of_card_le_two (by omega))
    rw [alpha_eq, hempty, Real.sSup_empty]
  · refine le_antisymm (alpha_nonpos n) ?_
    by_contra hneg
    push_neg at hneg
    have h := neg_le_alpha hn (show (0 : ℝ) < -(Erdos507.α n) / 2 by linarith)
    linarith

/- ### Corollaries about the problem statements in `507.lean` -/

/-- Any function that is `O`-dominated by `α` (in the sense of the repo's `≪`/`≫`
notation) is eventually zero. -/
private lemma eventually_zero_of_bigO_alpha {f : ℕ → ℝ}
    (h : f =O[Filter.atTop] Erdos507.α) : ∀ᶠ n in Filter.atTop, f n = 0 := by
  have hα : Erdos507.α = fun _ => (0 : ℝ) := funext alpha_eq_zero
  rw [hα] at h
  have h2 : f =ᶠ[Filter.atTop] 0 := Asymptotics.isBigO_zero_right_iff.mp h
  filter_upwards [h2] with n hn
  simpa using hn

private lemma lowerBest_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Erdos507.lowerBest n := by
  have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  exact div_pos (Real.log_pos h1) (pow_pos (by linarith) 2)

/-- The statement shape of `erdos_507.upper` is (trivially) satisfied by the zero
function: the formalized "upper bound for `α`" problem is degenerate. -/
theorem erdos_507_upper_answered :
    let ans := ((fun _ => (0 : ℝ)) : ℕ → ℝ)
    (Erdos507.α ≪ ans) ∧ (ans =o[Filter.atTop] Erdos507.upperBarrier) := by
  intro ans
  constructor
  · have h : Erdos507.α = ans := funext alpha_eq_zero
    rw [h]
    exact Asymptotics.isBigO_refl _ _
  · exact Asymptotics.isLittleO_zero _ _

/-- No answer whatsoever can make the statement of `erdos_507.lower` true:
`lowerBest` is eventually positive, but any `ans` with `ans ≪ α` is eventually zero,
and then `lowerBest =o[atTop] ans` fails. -/
theorem erdos_507_lower_unanswerable :
    ∀ ans : ℕ → ℝ, ¬ ((Erdos507.lowerBest =o[Filter.atTop] ans) ∧ (ans ≪ Erdos507.α)) := by
  rintro ans ⟨ho, hO⟩
  have h1 : ∀ᶠ n in Filter.atTop, ans n = 0 := eventually_zero_of_bigO_alpha hO
  have h1' : ans =ᶠ[Filter.atTop] 0 := by
    filter_upwards [h1] with n hn
    simpa using hn
  have hO2 : ans =O[Filter.atTop] (fun _ => (0 : ℝ)) :=
    Asymptotics.isBigO_zero_right_iff.mpr h1'
  have h2 : Erdos507.lowerBest =ᶠ[Filter.atTop] 0 :=
    Asymptotics.isBigO_zero_right_iff.mp (ho.trans_isBigO hO2).isBigO
  obtain ⟨n, hz, hn⟩ := (h2.and (Filter.eventually_ge_atTop 2)).exists
  exact (lowerBest_pos hn).ne' (by simpa using hz)

/-- `erdos_507.variants.lower_erdos` (tagged `research solved` in the source) is false
as stated: `α ≡ 0` cannot dominate the eventually-positive function `1/n²`. -/
theorem not_lower_erdos : ¬ (Erdos507.α ≫ (fun n ↦ 1 / (n : ℝ) ^ 2)) := by
  intro h
  have h1 := eventually_zero_of_bigO_alpha h
  obtain ⟨n, hz, hn⟩ := (h1.and (Filter.eventually_ge_atTop 1)).exists
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have : (0 : ℝ) < 1 / (n : ℝ) ^ 2 := by positivity
  exact this.ne' hz

/-- `erdos_507.variants.lower_kps82` (tagged `research solved` in the source) is false
as stated: `α ≡ 0` cannot dominate the eventually-positive function `log n / n²`. -/
theorem not_lower_kps82 : ¬ (Erdos507.lowerBest ≪ Erdos507.α) := by
  intro h
  have h1 := eventually_zero_of_bigO_alpha h
  obtain ⟨n, hz, hn⟩ := (h1.and (Filter.eventually_ge_atTop 2)).exists
  exact (lowerBest_pos hn).ne' hz
