module

public import A038098.Middle
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Integration of the zero-counting majorant for the two nonconstant parts
of the capped inverse-ordinate weight. -/
public section
namespace Sun.CubeAnalytic
open Real Set Filter MeasureTheory
open scoped Topology

@[expose] noncomputable def countMajorant (t : ℝ) : ℝ :=
  t/(2*π)*(log t-log (2*π)-1) + log t

private noncomputable def midPrimitive (t : ℝ) : ℝ :=
  (log t-log (2*π)-1)^2/(4*π)-(log t+1)*t⁻¹

private noncomputable def tailPrimitive (B t : ℝ) : ℝ :=
  -(B/π)*((log t-log (2*π))*t⁻¹)-B*((log t+1/2)*t⁻¹^2)

private theorem deriv_mid {t : ℝ} (ht : 0<t) :
    HasDerivAt midPrimitive (countMajorant t/t^2) t := by
  have l := Real.hasDerivAt_log ht.ne'
  have i := hasDerivAt_inv ht.ne'
  have h := ((((l.sub_const (log (2*π))).sub_const 1).pow 2).div_const (4*π)).sub
    ((l.add_const 1).mul i)
  convert! h using 1 <;> first | rfl | (unfold countMajorant; dsimp; field_simp; ring)

private theorem deriv_tail (B : ℝ) {t : ℝ} (ht : 0<t) :
    HasDerivAt (tailPrimitive B) (countMajorant t*(2*B/t^3)) t := by
  have l := Real.hasDerivAt_log ht.ne'
  have i := hasDerivAt_inv ht.ne'
  have p := ((l.sub_const (log (2*π))).mul i).const_mul (-(B/π))
  have q := ((l.add_const (1/2)).mul (i.pow 2)).const_mul B
  have h := p.sub q
  convert! h using 1 <;> first | rfl | (unfold countMajorant; dsimp; field_simp; ring)

private theorem limit_tail (B : ℝ) : Tendsto (tailPrimitive B) atTop (𝓝 0) := by
  have i : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have l : Tendsto (fun t : ℝ => log t*t⁻¹) atTop (𝓝 0) := by
    have h := tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h.congr (fun t => by simp [div_eq_mul_inv])
  have h := (((l.sub (i.const_mul (log (2*π)))).const_mul (-(B/π)))).sub
    (((l.mul i).add ((i.pow 2).const_mul (1/2))).const_mul B)
  simp at h
  refine h.congr (fun t => ?_)
  dsimp [tailPrimitive]
  ring

/-- Rosser's majorant can be integrated without using any lower bound for the
zero count. The final endpoint correction is (log A+1)/A - 1/(2B). -/
theorem integrate_zero_count {A B : ℝ} (ha : 0<A) (hab : A≤B) (N : ℝ → ℝ)
    (hN : ∀ t, A≤t → 0≤N t ∧ N t≤countMajorant t) :
    (∫ t in Ioc A B, N t/t^2) + (∫ t in Ioi B, N t*(2*B/t^3)) ≤
    ((log B-log (2*π))^2 - (log A-log (2*π))^2 + 2*(log B-log (2*π))+
      2*(log A-log (2*π)))/(4*π) + (log A+1)/A - 1/(2*B) := by
  have hB : 0<B := ha.trans_le hab
  have hc : ContinuousOn (fun t : ℝ => countMajorant t/t^2) (Icc A B) := by
    intro t ht
    have ht0 : t ≠ 0 := (ha.trans_le ht.1).ne'
    unfold countMajorant
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hm : IntegrableOn (fun t : ℝ => countMajorant t/t^2) (Ioc A B) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hhead : (∫ t in Ioc A B, N t/t^2) ≤ midPrimitive B - midPrimitive A := by
    calc _ ≤ ∫ t in Ioc A B, countMajorant t/t^2 := by
          apply integral_mono_of_nonneg _ hm
          · exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ (fun t ht =>
              div_nonneg (hN t ht.1.le).1 (sq_nonneg _)))
          · exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ (fun t ht =>
              div_le_div_of_nonneg_right (hN t ht.1.le).2 (sq_nonneg _)))
         _ = _ := by
          rw [← intervalIntegral.integral_of_le hab]
          apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          · intro t ht
            rw [uIcc_of_le hab] at ht
            exact deriv_mid (ha.trans_le ht.1)
          · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hm
  have hder : ∀ t ∈ Ici B, HasDerivAt (tailPrimitive B) (countMajorant t*(2*B/t^3)) t :=
    fun t ht => deriv_tail B (hB.trans_le ht)
  have hpos (t : ℝ) (ht : t ∈ Ioi B) : 0 ≤ countMajorant t*(2*B/t^3) := by
    have ht0 := hB.trans ht
    have H := hN t (hab.trans ht.le)
    exact mul_nonneg (H.1.trans H.2) (by positivity)
  have htint := integrableOn_Ioi_deriv_of_nonneg' hder hpos (limit_tail B)
  have htail : (∫ t in Ioi B, N t*(2*B/t^3)) ≤ 0-tailPrimitive B B := by
    rw [← integral_Ioi_of_hasDerivAt_of_nonneg' hder hpos (limit_tail B)]
    apply integral_mono_of_nonneg _ htint
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
      intro t ht
      have ht0 := hB.trans ht
      exact mul_nonneg (hN t (hab.trans ht.le)).1 (by positivity)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
      intro t ht
      have ht0 := hB.trans ht
      exact mul_le_mul_of_nonneg_right (hN t (hab.trans ht.le)).2 (by positivity)
  apply (add_le_add hhead htail).trans_eq
  unfold midPrimitive tailPrimitive
  field_simp
  ring

end Sun.CubeAnalytic
#print axioms Sun.CubeAnalytic.integrate_zero_count
