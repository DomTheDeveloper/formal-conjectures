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

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section

/-!
# Short terminal arcs on the unit additive circle

For `0 < a < 1`, the arc represented by the real interval `(1-a, 1)` is open,
its endpoint closure is represented by `[1-a, 1]`, and both have normalized
Haar measure `a`.
-/

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace UnitAddCircle

/-- The open terminal arc of length `a` in `ℝ / ℤ`. -/
def openArc (a : ℝ) : Set UnitAddCircle :=
  ((↑) : ℝ → UnitAddCircle) '' Ioo (1 - a) 1

/-- The closed endpoint hull of `openArc a`. -/
def closedArc (a : ℝ) : Set UnitAddCircle :=
  ((↑) : ℝ → UnitAddCircle) '' Icc (1 - a) 1

private theorem coe_eq_coe_iff_of_mem_Ioc {x y : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) (hy : y ∈ Ioc (0 : ℝ) 1) :
    (x : UnitAddCircle) = (y : UnitAddCircle) ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg (AddCircle.equivIoc (1 : ℝ) 0) h
    rw [AddCircle.equivIoc_coe_eq hx, AddCircle.equivIoc_coe_eq hy] at h'
    exact congrArg Subtype.val h'
  · rintro rfl
    rfl

/-- `openArc a` is open. -/
theorem isOpen_openArc (a : ℝ) : IsOpen (openArc a) :=
  QuotientAddGroup.isOpenMap_coe isOpen_Ioo

/-- `closedArc a` is closed. -/
theorem isClosed_closedArc (a : ℝ) : IsClosed (closedArc a) :=
  (isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))).isClosed

/-- The open arc is contained in its endpoint closure. -/
theorem openArc_subset_closedArc (a : ℝ) : openArc a ⊆ closedArc a :=
  image_mono Ioo_subset_Icc_self

private theorem preimage_openArc_inter_Ioc {a : ℝ} (ha : a < 1) :
    ((↑) : ℝ → UnitAddCircle) ⁻¹' openArc a ∩ Ioc 0 1 = Ioo (1 - a) 1 := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, hxy⟩, hx⟩
    have hyIoc : y ∈ Ioc (0 : ℝ) 1 :=
      ⟨(sub_pos.mpr ha).trans hy.1, hy.2.le⟩
    have hxy' : y = x :=
      (coe_eq_coe_iff_of_mem_Ioc hyIoc hx).mp hxy
    simpa [hxy'] using hy
  · intro hx
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    exact ⟨(sub_pos.mpr ha).trans hx.1, hx.2.le⟩

private theorem preimage_closedArc_inter_Ioc {a : ℝ} (ha : a < 1) :
    ((↑) : ℝ → UnitAddCircle) ⁻¹' closedArc a ∩ Ioc 0 1 = Icc (1 - a) 1 := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, hxy⟩, hx⟩
    have hyIoc : y ∈ Ioc (0 : ℝ) 1 :=
      ⟨(sub_pos.mpr ha).trans_le hy.1, hy.2⟩
    have hxy' : y = x :=
      (coe_eq_coe_iff_of_mem_Ioc hyIoc hx).mp hxy
    simpa [hxy'] using hy
  · intro hx
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    exact ⟨(sub_pos.mpr ha).trans_le hx.1, hx.2⟩

/-- The open terminal arc has Haar measure `a`. -/
theorem volume_openArc {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    volume (openArc a) = ENNReal.ofReal a := by
  rw [AddCircle.add_projection_respects_measure (1 : ℝ) 0
    (isOpen_openArc a).measurableSet]
  rw [preimage_openArc_inter_Ioc ha1, Real.volume_Ioo]
  congr 1
  ring

/-- Adding the two endpoints does not change the Haar measure. -/
theorem volume_closedArc {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    volume (closedArc a) = ENNReal.ofReal a := by
  rw [AddCircle.add_projection_respects_measure (1 : ℝ) 0
    (isClosed_closedArc a).measurableSet]
  rw [preimage_closedArc_inter_Ioc ha1, Real.volume_Icc]
  congr 1
  ring

/-- The two endpoint conventions are equal almost everywhere. -/
theorem openArc_ae_eq_closedArc {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    openArc a =ᵐ[volume] closedArc a := by
  apply EventuallyLE.antisymm (openArc_subset_closedArc a).eventuallyLE
  rw [ae_le_set]
  exact measure_mono_null (diff_subset_iff.mpr (openArc_subset_closedArc a)) <| by
    rw [measure_diff (isOpen_openArc a).measurableSet (measure_ne_top _ _),
      volume_closedArc ha0 ha1, volume_openArc ha0 ha1]
    simp

end UnitAddCircle
