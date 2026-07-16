/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Tight

import FormalConjecturesForMathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed

/-!
# Lévy's convergence theorem

A compatibility backport for the mathlib snapshot pinned by formal-conjectures. The final
convergence theorem is specialized to real probability measures, which is exactly the form needed
by the one-dimensional central limit theorem used in the Voronovskaja proof.
-/

public section

open Filter BoundedContinuousFunction Real RCLike
open scoped Topology RealInnerProductSpace InnerProductSpace ENNReal

namespace MeasureTheory

private lemma tendsto_iSup_of_tendsto_limsup_compat {ι α β : Type*} [Nonempty ι]
    [ConditionallyCompleteLattice α] [CompleteLinearOrder β]
    [TopologicalSpace β] [FirstCountableTopology β] [OrderTopology β]
    {u : ι → α → β} {c : β}
    (h_all : ∀ i, Tendsto (u i) atTop (𝓝 c))
    (h_limsup : Tendsto (fun r : α ↦ limsup (fun i ↦ u i r) cofinite) atTop (𝓝 c))
    (h_anti : ∀ i, Antitone (u i)) :
    Tendsto (fun r : α ↦ ⨆ i, u i r) atTop (𝓝 c) := by
  classical
  let n0 : ι := Classical.choice (inferInstance : Nonempty ι)
  refine tendsto_order.mpr ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · filter_upwards with r
    have hc : c ≤ u n0 r := (h_anti n0).le_of_tendsto (h_all n0) r
    exact hb.trans_le (hc.trans (le_iSup (fun i ↦ u i r) n0))
  let b' := if h : (Set.Ioo c b).Nonempty then h.some else c
  have hb'b : b' < b := by
    simp only [b']
    split_ifs with h
    exacts [h.some_mem.2, hb]
  have hev : ∀ᶠ r in atTop, limsup (u · r) cofinite ≤ b' := by
    simp only [b']
    split_ifs with h
    · filter_upwards [(tendsto_order.1 h_limsup).2 _ h.some_mem.1] with r hr using hr.le
    · filter_upwards [(tendsto_order.1 h_limsup).2 b hb] with r hr
      contrapose! h
      exact ⟨limsup (u · r) cofinite, h, hr⟩
  simp only [eventually_atTop] at hev
  obtain ⟨r, hr⟩ := hev
  obtain ⟨b'', hb''b, hb''⟩ : ∃ b'' ∈ Set.Ico b' b, ∀ᶠ n in cofinite, u n r ≤ b'' := by
    rcases Set.eq_empty_or_nonempty (Set.Ioo b' b) with h | ⟨b'', hb'b'', hb''b⟩
    · refine ⟨b', ⟨le_rfl, hb'b⟩, ?_⟩
      have h_lt := eventually_lt_of_limsup_lt ((hr r le_rfl).trans_lt hb'b)
      filter_upwards [h_lt] with n hn
      contrapose! h
      exact ⟨u n r, h, hn⟩
    · refine ⟨b'', ⟨hb'b''.le, hb''b⟩, ?_⟩
      have h_lt := eventually_lt_of_limsup_lt ((hr r le_rfl).trans_lt hb'b'')
      filter_upwards [h_lt] with n hn using hn.le
  have A (n) : ∃ r, ∀ s ≥ r, u n s ≤ b'' := by
    suffices ∀ᶠ r in atTop, u n r ≤ b' by
      simp only [eventually_atTop] at this
      rcases this with ⟨r, hr⟩
      exact ⟨r, fun s hs ↦ (hr s hs).trans hb''b.1⟩
    simp only [b']
    split_ifs with h
    · filter_upwards [(tendsto_order.1 (h_all n)).2 _ h.some_mem.1] with r hr
      exact hr.le
    · filter_upwards [(tendsto_order.1 (h_all n)).2 b hb] with r hr
      contrapose! h
      exact ⟨u n r, h, hr⟩
  choose rs hrs using A
  simp only [eventually_atTop]
  refine ⟨r ⊔ ⨆ n : {n | b'' < u n r}, rs n, fun v hv ↦ ?_⟩
  apply lt_of_le_of_lt (iSup_le fun n ↦ ?_) hb''b.2
  by_cases hn : b'' < u n r
  · refine hrs n v ?_
    calc
      rs n = rs (⟨n, by simp [hn]⟩ : {n | b'' < u n r}) := rfl
      _ ≤ ⨆ n : {n | b'' < u n r}, rs n := by
        refine le_ciSup (f := fun x : {n | b'' < u n r} ↦ rs x) ?_ ⟨n, by simp [hn]⟩
        have : Finite {n | b'' < u n r} := by simpa using! hb''
        exact Finite.bddAbove_range _
      _ ≤ r ⊔ ⨆ n : {n | b'' < u n r}, rs n := le_sup_right
      _ ≤ v := hv
  · refine (h_anti n ?_).trans (not_lt.mp hn)
    calc
      r ≤ r ⊔ ⨆ n : {n | b'' < u n r}, rs n := le_sup_left
      _ ≤ v := hv

private lemma Nat_tendsto_iSup_of_tendsto_limsup_compat {α β : Type*}
    [ConditionallyCompleteLattice α] [CompleteLinearOrder β]
    [TopologicalSpace β] [FirstCountableTopology β] [OrderTopology β]
    {u : ℕ → α → β} {c : β}
    (h_all : ∀ n, Tendsto (u n) atTop (𝓝 c))
    (h_limsup : Tendsto (fun r : α ↦ limsup (fun n ↦ u n r) atTop) atTop (𝓝 c))
    (h_anti : ∀ n, Antitone (u n)) :
    Tendsto (fun r : α ↦ ⨆ n, u n r) atTop (𝓝 c) := by
  rw [← Nat.cofinite_eq_atTop] at h_limsup
  exact tendsto_iSup_of_tendsto_limsup_compat h_all h_limsup h_anti

private lemma isTightMeasureSet_range_of_tendsto_limsup_inner_compat
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [MeasurableSpace E] [BorelSpace E]
    {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)]
    (h : ∀ y, Tendsto
      (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_of_inner_tendsto fun z ↦ ?_
  simp_rw [iSup_range]
  refine Nat_tendsto_iSup_of_tendsto_limsup_compat (fun n ↦ ?_) (h z) (fun n u v huv ↦ by gcongr)
  have h_tight : IsTightMeasureSet {(μ n).map (fun x ↦ ⟪z, x⟫_𝕜)} :=
    isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h_tight
  have h_map r : (μ n).map (fun x ↦ ⟪z, x⟫_𝕜) {x | r < ‖x‖} =
      μ n {x | r < ‖⟪z, x⟫_𝕜‖} := by
    rw [Measure.map_apply (by fun_prop)]
    · simp
    · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
  simpa [h_map] using h_tight

private lemma isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one_compat
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [MeasurableSpace E] [BorelSpace E]
    {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)]
    (h : ∀ y, ‖y‖ = 1 → Tendsto
      (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_range_of_tendsto_limsup_inner_compat fun y ↦ ?_
  by_cases hy : y = 0
  · simp only [hy, inner_zero_left]
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 0] with r hr
    simp [not_lt.mpr hr]
  have h' : Tendsto
      (fun r : ℝ ↦ limsup
        (fun n ↦ μ n {x | ‖y‖⁻¹ * r < ‖⟪(‖y‖⁻¹ : 𝕜) • y, x⟫_𝕜‖}) atTop)
      atTop (𝓝 0) := by
    specialize h ((‖y‖⁻¹ : 𝕜) • y) ?_
    · simp only [norm_smul, norm_inv, norm_algebraMap', Real.norm_eq_abs, abs_norm]
      rw [inv_mul_cancel₀ (by positivity)]
    exact h.comp <| (tendsto_const_mul_atTop_of_pos (by positivity)).mpr tendsto_id
  convert h' using 7 with r n x
  rw [inner_smul_left]
  simp only [map_inv₀, RCLike.conj_ofReal, norm_mul, norm_inv, norm_algebraMap', norm_norm]
  rw [mul_lt_mul_iff_right₀]
  positivity

private lemma isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one_compat
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [MeasurableSpace E] [BorelSpace E]
    {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)]
    (h : ∀ y, ‖y‖ = 1 → Tendsto
      (fun r : ℝ ↦ limsup (fun n ↦ (μ n).real {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0))
    (C : ℝ≥0) (hμ : ∀ᶠ n in atTop, μ n Set.univ ≤ C) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one_compat fun z hz ↦ ?_
  have h_ofReal (r : ℝ) :
      limsup (fun n ↦ μ n {x | r < ‖⟪z, x⟫_𝕜‖}) atTop =
        ENNReal.ofReal (limsup (fun n ↦ (μ n).real {x | r < ‖⟪z, x⟫_𝕜‖}) atTop) := by
    simp_rw [measureReal_def]
    rw [ENNReal.ofReal_limsup_toReal (C := C)]
    filter_upwards [hμ] with n hn using (measure_mono (Set.subset_univ _)).trans hn
  simpa only [h_ofReal, ← ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (h z hz)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma isTightMeasureSet_of_tendsto_charFun {μ : ℕ → Measure E}
    [∀ i, IsProbabilityMeasure (μ i)] {f : E → ℂ} (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (f t))) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one_compat
    (fun z hz ↦ ?_) 1 (.of_forall fun _ ↦ by simp)
  have h_le_4 n r (hr : 0 < r) :
      2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖ ≤ 4 := by
    have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
    calc
      2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖
          ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ‖1 - charFun (μ n) (t • z)‖ := by
            grw [neg_mul, intervalIntegral.norm_integral_le_integral_norm hr']
      _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, 2 := by
            gcongr
            rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
            refine integral_mono_of_nonneg ?_ (by fun_prop) ?_
            · exact ae_of_all _ fun _ ↦ by positivity
            · exact ae_of_all _ fun _ ↦ norm_one_sub_charFun_le_two
      _ ≤ 4 := by
            simp only [intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul]
            field_simp
            norm_num
  have h_le n r (hr : 0 < r) : (μ n).real {x | r < |⟪z, x⟫|} ≤
      2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖ :=
    measureReal_abs_inner_gt_le_integral_charFun hr
  have h_limsup_le r (hr : 0 < r) :
      limsup (fun n ↦ (μ n).real {x | r < |⟪z, x⟫|}) atTop ≤
        2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖ := by
    calc
      limsup (fun n ↦ (μ n).real {x | r < |⟪z, x⟫|}) atTop
          ≤ limsup (fun n ↦ 2⁻¹ * r *
              ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖) atTop := by
            refine limsup_le_limsup (.of_forall fun n ↦ h_le n r hr) ?_ ?_
            · exact IsCoboundedUnder.of_frequently_ge <| .of_forall fun _ ↦ ENNReal.toReal_nonneg
            · refine ⟨4, ?_⟩
              simp only [eventually_map, eventually_atTop]
              exact ⟨0, fun n _ ↦ h_le_4 n r hr⟩
      _ = 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖ := by
            refine ((Tendsto.norm ?_).const_mul _).limsup_eq
            simp only [neg_mul]
            have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
            simp_rw [intervalIntegral.integral_of_le hr']
            refine tendsto_integral_of_dominated_convergence (fun _ ↦ 2) ?_ (by fun_prop) ?_ ?_
            · exact fun _ ↦ Measurable.aestronglyMeasurable <| by fun_prop
            · exact fun _ ↦ ae_of_all _ fun _ ↦ norm_one_sub_charFun_le_two
            · exact ae_of_all _ fun _ ↦ tendsto_const_nhds.sub (h _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (h := fun r ↦ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖) ?_ ?_ ?_
  rotate_left
  · filter_upwards [eventually_gt_atTop 0] with r hr
    refine le_limsup_of_le ?_ fun u hu ↦ ?_
    · refine ⟨4, ?_⟩
      simp only [eventually_map, eventually_atTop]
      exact ⟨0, fun n _ ↦ (h_le n r hr).trans (h_le_4 n r hr)⟩
    · exact ENNReal.toReal_nonneg.trans hu.exists.choose_spec
  · filter_upwards [eventually_gt_atTop 0] with r hr using h_limsup_le r hr
  have hf_tendsto := hf.tendsto
  rw [Metric.tendsto_nhds_nhds] at hf_tendsto
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hf0 : f 0 = 1 := by symm; simpa using h 0
  simp only [gt_iff_lt, dist_eq_norm_sub', zero_sub, norm_neg, hf0] at hf_tendsto
  simp only [ge_iff_le, neg_mul, dist_zero_right, norm_mul, norm_inv,
    Real.norm_ofNat, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  obtain ⟨δ, hδ, hδ_lt⟩ : ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ < δ → ‖1 - f x‖ < ε / 4 :=
    hf_tendsto (ε / 4) (by positivity)
  refine ⟨4 * δ⁻¹, fun r hrδ ↦ ?_⟩
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hrδ
  have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
  have h_le_Ioc x (hx : x ∈ Set.Ioc (-(2 * r⁻¹)) (2 * r⁻¹)) : ‖1 - f (x • z)‖ ≤ ε / 4 := by
    refine (hδ_lt ?_).le
    simp only [norm_smul, Real.norm_eq_abs, mul_one, hz]
    calc
      |x| ≤ 2 * r⁻¹ := by grind
      _ < δ := by
        rw [← lt_div_iff₀' (by positivity), inv_lt_comm₀ hr (by positivity)]
        refine lt_of_lt_of_le ?_ hrδ
        field_simp
        norm_num
  rw [abs_of_nonneg hr.le]
  calc
    2⁻¹ * r * ‖∫ t in -(2 * r⁻¹)..2 * r⁻¹, 1 - f (t • z)‖
        ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ‖1 - f (t • z)‖ := by
          grw [intervalIntegral.norm_integral_le_integral_norm hr']
    _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ε / 4 := by
          gcongr
          rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
          have hf_meas : Measurable f := by
            refine measurable_of_tendsto_metrizable (f := fun n t ↦ charFun (μ n) t) (by fun_prop) ?_
            rwa [tendsto_pi_nhds]
          refine integral_mono_ae ?_ (by fun_prop) ?_
          · refine Integrable.mono' (integrable_const (ε / 4)) ?_ ?_
            · exact Measurable.aestronglyMeasurable <| by fun_prop
            · simpa using ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
          · exact ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
    _ = ε / 2 := by simp; field
    _ < ε := by simp [hε]

private lemma ProbabilityMeasure.tendsto_of_tight_of_tendsto_charFun_real
    {ι : Type*} {𝓕 : Filter ι} {μ : ι → ProbabilityMeasure ℝ}
    (h_tight : IsTightMeasureSet {(μ n : Measure ℝ) | n}) {μ₀ : ProbabilityMeasure ℝ}
    (h : ∀ t : ℝ, Tendsto (fun n ↦ charFun (μ n : Measure ℝ) t) 𝓕
      (𝓝 (charFun (μ₀ : Measure ℝ) t))) :
    Tendsto μ 𝓕 (𝓝 μ₀) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable ℝ
  obtain rfl | _ := 𝓕.eq_or_neBot
  · simp
  refine (Filter.tendsto_iff_ultrafilter _ _ _).2 fun U hU ↦ ?_
  have h_compact : IsCompact (closure {μ n | n}) :=
    isCompact_closure_of_isTightMeasureSet (by simpa using h_tight)
  obtain ⟨μ', -, hμ' : Tendsto _ _ _⟩ := h_compact.ultrafilter_le_nhds (U.map μ)
    (.trans (by simp) (monotone_principal subset_closure))
  have hmeasure : (μ' : Measure ℝ) = (μ₀ : Measure ℝ) := by
    apply Measure.ext_of_charFun
    funext t
    have hsub : Tendsto (fun n ↦ charFun (μ n : Measure ℝ) t) (U : Filter ι)
        (𝓝 (charFun (μ' : Measure ℝ) t)) := by
      rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at hμ'
      simpa only [charFun_eq_integral_innerProbChar] using hμ' (innerProbChar t)
    exact tendsto_nhds_unique hsub ((h t).comp hU)
  have hprob : μ' = μ₀ := ProbabilityMeasure.toMeasure_injective hmeasure
  simpa [hprob] using hμ'

variable {μ : ℕ → ProbabilityMeasure ℝ} {μ₀ : ProbabilityMeasure ℝ}

lemma ProbabilityMeasure.tendsto_of_tendsto_charFun
    (h : ∀ t : ℝ, Tendsto (fun n ↦ charFun (μ n : Measure ℝ) t) atTop
      (𝓝 (charFun (μ₀ : Measure ℝ) t))) :
    Tendsto μ atTop (𝓝 μ₀) := by
  have hcont : ContinuousAt (charFun (μ₀ : Measure ℝ)) 0 := by
    have hc : Continuous (charFun (μ₀ : Measure ℝ)) := by
      refine contDiff_zero.1 (contDiff_charFun ?_)
      simpa using (by fun_prop)
    exact hc.continuousAt
  have htight : IsTightMeasureSet {(μ n : Measure ℝ) | n} :=
    isTightMeasureSet_of_tendsto_charFun hcont h
  exact tendsto_of_tight_of_tendsto_charFun_real htight h

lemma ProbabilityMeasure.tendsto_iff_tendsto_charFun :
    Tendsto μ atTop (𝓝 μ₀) ↔
      ∀ t : ℝ, Tendsto (fun n ↦ charFun (μ n : Measure ℝ) t) atTop
        (𝓝 (charFun (μ₀ : Measure ℝ) t)) := by
  refine ⟨fun h t ↦ ?_, ProbabilityMeasure.tendsto_of_tendsto_charFun⟩
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at h
  simpa only [charFun_eq_integral_innerProbChar] using h (innerProbChar t)

end MeasureTheory
