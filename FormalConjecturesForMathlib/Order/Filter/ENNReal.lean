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

public import Mathlib.Order.Filter.ENNReal

/-!
# ENNReal limsup compatibility

Small compatibility backport for the mathlib snapshot pinned by formal-conjectures.
-/

public section

open Filter
open scoped NNReal

namespace ENNReal

variable {α : Type*} {f : Filter α}

lemma ofReal_limsup_compat {u : α → ℝ}
    (h₁ : IsCoboundedUnder (· ≤ ·) f u := by isBoundedDefault)
    (h₂ : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    ENNReal.ofReal (limsup u f) = limsup (fun a ↦ ENNReal.ofReal (u a)) f := by
  refine ENNReal.eq_of_forall_le_nnreal_iff fun r ↦ ?_
  simp only [ofReal_le_coe]
  rw [limsup_le_iff, limsup_le_iff]
  constructor
  · rintro h (_ | x) hx
    · simp
    filter_upwards [h x (by simpa using hx)] with a ha
    obtain ha₀ | ha₀ := le_total (u a) 0
    · simpa [ofReal_of_nonpos, *] using hx.bot_lt
    · simp [ofReal_lt_coe_iff, *]
  · rintro h x hx
    have hx₀ : 0 < x := hx.trans_le' (by simp)
    have hrx : (r : ℝ≥0∞) < ENNReal.ofReal x :=
      (ENNReal.lt_ofReal_iff_toReal_lt ENNReal.coe_ne_top).2 (by simpa using hx)
    filter_upwards [h (.ofReal x) hrx] with a ha
    exact (toReal_lt_of_lt_ofReal ha).trans_le' (by simp [toReal_ofReal'])

lemma ofReal_limsup_toReal_compat [f.NeBot] {u : α → ℝ≥0∞} {C : ℝ≥0}
    (hf : ∀ᶠ a in f, u a ≤ C) :
    ENNReal.ofReal (limsup (fun a ↦ (u a).toReal) f) = limsup u f := by
  have h₁ : IsCoboundedUnder (· ≤ ·) f (fun a ↦ (u a).toReal) :=
    IsCoboundedUnder.of_frequently_ge <| .of_forall fun _ ↦ by positivity
  have h₂ : IsBoundedUnder (· ≤ ·) f (fun a ↦ (u a).toReal) := by
    refine isBoundedUnder_of_eventually_le (a := C) ?_
    filter_upwards [hf] with a ha
    exact ENNReal.toReal_le_coe_of_le_coe ha
  refine (ofReal_limsup_compat h₁ h₂).trans (limsup_congr ?_)
  filter_upwards [hf] with x hx
  exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp : (C : ℝ≥0∞) ≠ ∞) hx)

end ENNReal
