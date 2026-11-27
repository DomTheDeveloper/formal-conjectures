module

public import A038098.ZeroCounts

/-! Summing a truncated inverse-ordinate weight against a zero count. Zeros
are allowed arbitrary nonnegative multiplicities. -/
public section
namespace Sun.CubeAnalytic
open Real Set Filter MeasureTheory
open scoped Topology

@[expose] noncomputable def ordinateWeight (A B u : ℝ) : ℝ :=
  min (1/A) (min (1/u) (B/u^2))

private noncomputable def midPiece (u m : ℝ) : ℝ → ℝ :=
  (Ioi u).indicator (fun t => m/t^2)

private noncomputable def tailPiece (u m B : ℝ) : ℝ → ℝ :=
  (Ioi u).indicator (fun t => m*(2*B/t^3))

private theorem head_integrable (m : ℝ) {a b : ℝ} (ha : 0<a) :
    IntegrableOn (fun t : ℝ => m/t^2) (Ioc a b) := by
  refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
  exact continuousOn_const.div (continuousOn_pow 2) (fun x hx => (pow_pos (ha.trans_le hx.1) 2).ne')

private theorem head_value (m : ℝ) {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    (∫ t in Ioc a b, m/t^2) = m*(1/a-1/b) := by
  rw [← intervalIntegral.integral_of_le hab]
  have der (t : ℝ) (ht : t∈uIcc a b) :
      HasDerivAt (fun v : ℝ => -m*v⁻¹) (m/t^2) t := by
    rw [uIcc_of_le hab] at ht
    have ht0 := (ha.trans_le ht.1).ne'
    have he : m/t^2 = -m * -(t^2)⁻¹ := by simp [div_eq_mul_inv]
    rw [he]
    exact (hasDerivAt_inv ht0).const_mul (-m)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt der
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 (head_integrable _ ha))]
  ring

private theorem tail_der (m B : ℝ) {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun v : ℝ => -(m*B)*(v^2)⁻¹) (m*(2*B/t^3)) t := by
  have he : m*(2*B/t^3) = -(m*B)*(-(2*t^1)/(t^2)^2) := by
    field_simp [ht.ne']
    ring
  rw [he]
  convert! ((hasDerivAt_pow 2 t).inv (by positivity)).const_mul (-(m*B)) using 1 <;> simp

private theorem tail_lim (m B : ℝ) :
    Tendsto (fun v : ℝ => -(m*B)*(v^2)⁻¹) atTop (𝓝 0) := by
  simpa using (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (n := 2) two_ne_zero)).const_mul (-(m*B))

private theorem tail_integrable {m B a : ℝ} (hm : 0≤m) (hB : 0<B) (ha : 0<a) :
    IntegrableOn (fun t : ℝ => m*(2*B/t^3)) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun t ht => tail_der m B (ha.trans_le ht))
    (fun t ht => by have ht0 := ha.trans ht; positivity) (tail_lim m B)

private theorem pieces {u m A B : ℝ} (hu : 0<u) (hm : 0≤m) (ha : 0<A) (hab : A≤B) :
    m*ordinateWeight A B u = (∫ t in Ioc A B, midPiece u m t) +
      ∫ t in Ioi B, tailPiece u m B t := by
  have hB := ha.trans_le hab
  unfold midPiece tailPiece
  rw [setIntegral_indicator measurableSet_Ioi,Ioc_inter_Ioi,
    setIntegral_indicator measurableSet_Ioi,Ioi_inter_Ioi]
  have hmax : 0<max B u := hB.trans_le (le_max_left _ _)
  have ht := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t ht => tail_der m B (hmax.trans_le ht)) (fun t ht => by
      have ht0 := hmax.trans ht; positivity) (tail_lim m B)
  rw [ht]
  have hid : 1/u=u/u^2 := by field_simp
  by_cases h : u≤A
  · rw [max_eq_left h,max_eq_left (h.trans hab),head_value _ ha hab,ordinateWeight,
      min_eq_left (show 1/u≤B/u^2 by rw [hid]; exact div_le_div_of_nonneg_right (h.trans hab) (sq_nonneg _)),
      min_eq_left (one_div_le_one_div_of_le hu h)]
    field_simp
    ring
  · have hau : A≤u := le_of_not_ge h
    rw [max_eq_right hau]
    by_cases hl : u<B
    · rw [max_eq_left hl.le,head_value _ hu hl.le,ordinateWeight,
        min_eq_left (show 1/u≤B/u^2 by rw [hid]; exact div_le_div_of_nonneg_right hl.le (sq_nonneg _)),
        min_eq_right (one_div_le_one_div_of_le ha hau)]
      field_simp
      ring
    · have hbu : B≤u := le_of_not_gt hl
      have hshort : B/u^2≤1/u := by rw [hid]; exact div_le_div_of_nonneg_right hbu (sq_nonneg _)
      rw [max_eq_right hbu,Ioc_eq_empty hl,Measure.restrict_empty,integral_zero_measure,zero_add,
        ordinateWeight,min_eq_right hshort,min_eq_right (hshort.trans (one_div_le_one_div_of_le ha hau))]
      field_simp
      ring

@[expose] noncomputable def counted {ι : Type*} (S : Finset ι) (g m : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ S, if g i<t then m i else 0

/-- Any finite set of positive ordinates obeying the zero-count majorant
satisfies the integrated bound, with each multiplicity counted explicitly. -/
theorem sum_weight_le {ι : Type*} (S : Finset ι) (g m : ι → ℝ) {A B : ℝ}
    (ha : 0<A) (hab : A≤B) (hg : ∀ i∈S,0<g i) (hm : ∀ i∈S,0≤m i)
    (hcount : ∀ t, A≤t → counted S g m t ≤ countMajorant t) :
    (∑ i ∈ S, m i*ordinateWeight A B (g i)) ≤
      ((log B-log (2*π))^2-(log A-log (2*π))^2+2*(log B-log (2*π))+
        2*(log A-log (2*π)))/(4*π) + (log A+1)/A - 1/(2*B) := by
  classical
  have hB := ha.trans_le hab
  have h₁ : ∀ i∈S, IntegrableOn (midPiece (g i) (m i)) (Ioc A B) :=
    fun i _ => (head_integrable _ ha).indicator measurableSet_Ioi
  have h₂ : ∀ i∈S, IntegrableOn (tailPiece (g i) (m i) B) (Ioi B) :=
    fun i hi => (tail_integrable (hm i hi) hB hB).indicator measurableSet_Ioi
  have hmideq (t : ℝ) : (∑ i∈S, midPiece (g i) (m i) t) = counted S g m t/t^2 := by
    unfold counted
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : g i<t <;> simp [midPiece,Set.indicator,Set.mem_Ioi,h]
  have htaileq (t : ℝ) : (∑ i∈S, tailPiece (g i) (m i) B t) = counted S g m t*(2*B/t^3) := by
    unfold counted
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : g i<t <;> simp [tailPiece,Set.indicator,Set.mem_Ioi,h]
  calc _ = (∑ i∈S, ∫ t in Ioc A B, midPiece (g i) (m i) t) +
           ∑ i∈S, ∫ t in Ioi B, tailPiece (g i) (m i) B t := by
           rw [← Finset.sum_add_distrib]
           exact Finset.sum_congr rfl fun i hi => pieces (hg i hi) (hm i hi) ha hab
       _ = (∫ t in Ioc A B, counted S g m t/t^2) +
           ∫ t in Ioi B, counted S g m t*(2*B/t^3) := by
           rw [← integral_finsetSum S h₁,← integral_finsetSum S h₂]
           simp_rw [hmideq,htaileq]
       _ ≤ _ := integrate_zero_count ha hab _ (fun t ht => ⟨by
           unfold counted
           apply Finset.sum_nonneg
           intro i hi
           split_ifs <;> simp [hm i hi], hcount t ht⟩)

/-- The count bound on finite subsets gives the full convergent sum of the
weighted ordinates, even when the index type includes multiplicities. -/
theorem tsum_ordinateWeight_le {ι : Type*} (g m : ι → ℝ) {A B : ℝ}
    (ha : 0<A) (hab : A≤B) (hg : ∀ i, 0<g i) (hm : ∀ i, 0≤m i)
    (hcount : ∀ (S : Finset ι) (t : ℝ), A≤t → counted S g m t ≤ countMajorant t) :
    Summable (fun i => m i*ordinateWeight A B (g i)) ∧
    (∑' i, m i*ordinateWeight A B (g i)) ≤
      ((log B-log (2*π))^2-(log A-log (2*π))^2+2*(log B-log (2*π))+
        2*(log A-log (2*π)))/(4*π) + (log A+1)/A - 1/(2*B) := by
  have hB := ha.trans_le hab
  have hn (i : ι) : 0 ≤ m i*ordinateWeight A B (g i) := by
    have hgi := hg i
    apply mul_nonneg (hm i)
    exact le_min (by positivity) (le_min (by positivity) (by positivity))
  have hf (S : Finset ι) := sum_weight_le S g m ha hab (fun i _ => hg i)
    (fun i _ => hm i) (hcount S)
  exact ⟨summable_of_sum_le hn hf, Real.tsum_le_of_sum_le hn hf⟩

end Sun.CubeAnalytic
#print axioms Sun.CubeAnalytic.sum_weight_le
#print axioms Sun.CubeAnalytic.tsum_ordinateWeight_le
