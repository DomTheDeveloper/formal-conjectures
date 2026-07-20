from pathlib import Path
import runpy


def replace_once(path: Path, old: str, new: str, label: str) -> None:
    text = path.read_text()
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected one occurrence, found {count}")
    path.write_text(text.replace(old, new, 1))


moments = Path(
    "FormalConjecturesForMathlib/Probability/Distributions/PoweredBinomialMoments.lean"
)
replace_once(
    moments,
    """  have hinv : 0 < 1 / bernoulliStdDev p := one_div_pos.mpr hs
  positivity
""",
    """  have hinv : 0 < 1 / bernoulliStdDev p := one_div_pos.mpr hs
  have hnormNN : 0 < ‖(1 / bernoulliStdDev p : ℝ)‖₊ := by
    exact_mod_cast (norm_pos_iff.mpr (one_div_ne_zero (ne_of_gt hs)))
  positivity
""",
    "moments strict parameter positivity",
)
replace_once(
    moments,
    """      have hq1 : q ≤ 1 := by
        dsimp [q]
        rw [exp_le_one_iff]
        positivity
""",
    """      have hq1 : q ≤ 1 := by
        dsimp [q]
        rw [exp_le_one_iff]
        have hfrac : 0 ≤ t ^ 2 / (2 * c) := by positivity
        linarith
""",
    "moments exponential upper bound",
)

second = Path(
    "FormalConjecturesForMathlib/Probability/Distributions/PoweredBinomialSecondMoment.lean"
)
replace_once(
    second,
    """  have hinv : 0 < 1 / bernoulliStdDev p := one_div_pos.mpr hs
  positivity
""",
    """  have hinv : 0 < 1 / bernoulliStdDev p := one_div_pos.mpr hs
  have hnormNN : 0 < ‖(1 / bernoulliStdDev p : ℝ)‖₊ := by
    exact_mod_cast (norm_pos_iff.mpr (one_div_ne_zero (ne_of_gt hs)))
  positivity
""",
    "second strict parameter positivity",
)
replace_once(
    second,
    """  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [exp_le_one_iff]
    positivity
""",
    """  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [exp_le_one_iff]
    have hfrac : 0 ≤ t / (2 * c) := by positivity
    linarith
""",
    "second exponential upper bound",
)
old_abs = """      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg n)) measureReal_nonneg)]
"""
new_abs = """      have hprod0 : 0 ≤ (Real.sqrt n)⁻¹ *
          poweredStandardizedBinomialSecondMomentTail n p α hα t :=
        mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg n)) measureReal_nonneg
      rw [Real.norm_eq_abs, abs_of_nonneg hprod0]
"""
text = second.read_text()
count = text.count(old_abs)
if count != 2:
    raise SystemExit(f"second absolute-value normalization: expected two occurrences, found {count}")
second.write_text(text.replace(old_abs, new_abs))


discrete = Path("FormalConjectures/Paper/VoronovskajaDiscreteLaw.lean")
replace_once(
    discrete,
    """private theorem sum_bezierWeight_range (n m : ℕ) (α x : ℝ) :
    ∑ k ∈ Finset.range m, bezierWeight n k α x =
      1 - (bernsteinTail n m).eval x ^ α := by
  rw [show (∑ k ∈ Finset.range m, bezierWeight n k α x) =
      ∑ k ∈ Finset.range m,
        ((bernsteinTail n k).eval x ^ α -
          (bernsteinTail n (k + 1)).eval x ^ α) by rfl]
  rw [sum_range_sub_succ]
  simp [bernsteinTail_zero]
""",
    """private theorem sum_bezierWeight_range (n m : ℕ) (α x : ℝ) :
    ∑ k ∈ Finset.range m, bezierWeight n k α x =
      1 - (bernsteinTail n m).eval x ^ α := by
  simp only [bezierWeight]
  rw [sum_range_sub_succ]
  simp [bernsteinTail_zero]
""",
    "discrete weight telescoping",
)
replace_once(
    discrete,
    "          simpa only [Finset.sum_univ] using\n",
    "          simpa using\n",
    "discrete ENNReal finite sum",
)
text = discrete.read_text()
count = text.count("rw [Fin.sum_univ_eq_sum_range]")
if count != 3:
    raise SystemExit(f"discrete Fin sum orientation: expected three occurrences, found {count}")
discrete.write_text(text.replace(
    "rw [Fin.sum_univ_eq_sum_range]", "rw [← Fin.sum_univ_eq_sum_range]"
))
replace_once(
    discrete,
    "  unfold standardizeBinomial\n",
    "  dsimp [standardizeBinomial]\n",
    "discrete standardization beta reduction",
)
replace_once(
    discrete,
    """      · obtain ⟨m, hm, hfilter⟩ := ih
        refine ⟨m, hm.trans (Nat.le_succ N), ?_⟩
        simp [Finset.range_succ, hN, hfilter]
""",
    """      · obtain ⟨m, hm, hfilter⟩ := ih
        refine ⟨m, hm.trans (Nat.le_succ N), ?_⟩
        rw [Finset.range_add_one, Finset.filter_insert]
        simp [hN, hfilter]
""",
    "discrete filtered initial segment",
)
replace_once(
    discrete,
    """private theorem binomialPMF_toReal_eq_bernstein
    (n : ℕ) (x : I) (k : Fin (n + 1)) :
    ((binomialPMF n x) k).toReal =
      (bernsteinPolynomial ℝ n k).eval (x : ℝ) := by
  simp only [binomialPMF, PMF.binomial_apply, bernsteinPolynomial,
    Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
  have hq : ((1 : ℝ≥0∞) - (toNNReal x : ℝ≥0∞)).toReal = 1 - (x : ℝ) := by
    rw [ENNReal.toReal_sub_of_le]
    · simp
    · simpa using x.2.2
    · simp
  simp [hq]
  ring
""",
    """private theorem binomialPMF_toReal_eq_bernstein
    (n : ℕ) (x : I) (k : Fin (n + 1)) :
    ((binomialPMF n x) k).toReal =
      (bernsteinPolynomial ℝ n k).eval (x : ℝ) := by
  rw [binomialPMF_apply_toReal]
  simp [bernsteinPolynomial]
  ring_nf
""",
    "discrete binomial mass identity",
)
replace_once(
    discrete,
    """private theorem standardizedBinomialMeasure_eq_pmf_map
    (n : ℕ) (x : I) :
    standardizedBinomialMeasure n x =
      ((binomialPMF n x).map
        (fun k => standardizeBinomial n x ((k : ℕ) : ℝ))).toMeasure := by
  have hcast : Measurable (fun k : Fin (n + 1) ↦ (k : ℝ)) := .of_discrete
  have hstd : Measurable (standardizeBinomial n x) :=
    (continuous_standardizeBinomial n x).measurable
  rw [standardizedBinomialMeasure, binomialRealMeasure]
  rw [Measure.map_map hstd hcast]
  simpa [Function.comp_def] using
    (PMF.toMeasure_map (p := binomialPMF n x)
      (f := fun k : Fin (n + 1) =>
        standardizeBinomial n x ((k : ℕ) : ℝ)) (.of_discrete))
""",
    """private theorem standardizedBinomialMeasure_eq_pmf_map
    (n : ℕ) (x : I) :
    standardizedBinomialMeasure n x =
      ((binomialPMF n x).map
        (fun k => standardizeBinomial n x ((k : ℕ) : ℝ))).toMeasure := by
  have hcast : Measurable (fun k : Fin (n + 1) ↦ (k : ℝ)) := .of_discrete
  have hstd : Measurable (standardizeBinomial n x) :=
    (continuous_standardizeBinomial n x).measurable
  rw [standardizedBinomialMeasure, binomialRealMeasure]
  rw [Measure.map_map hstd hcast]
  change (binomialPMF n x).toMeasure.map
      (fun k : Fin (n + 1) => standardizeBinomial n x ((k : ℕ) : ℝ)) =
    ((binomialPMF n x).map
      (fun k : Fin (n + 1) => standardizeBinomial n x ((k : ℕ) : ℝ))).toMeasure
  exact PMF.toMeasure_map
    (fun k : Fin (n + 1) => standardizeBinomial n x ((k : ℕ) : ℝ))
    (binomialPMF n x) Measurable.of_discrete
""",
    "discrete standardized-binomial map",
)
replace_once(
    discrete,
    """  rw [standardizedBezierMeasure, standardizedBezierPMF,
    cdf_pmf_map_eq_sum (bezierPMF n α hα x)
      (fun k => standardizeBinomial n x ((k : ℕ) : ℝ)) Measurable.of_discrete]
""",
    """  rw [standardizedBezierMeasure, standardizedBezierPMF, PMF.map_comp]
  rw [cdf_pmf_map_eq_sum (bezierPMF n α hα x)
    (fun k => standardizeBinomial n x ((k : ℕ) : ℝ)) Measurable.of_discrete]
""",
    "discrete Bezier CDF map normalization",
)
replace_once(
    discrete,
    """  rw [standardizedBinomialMeasure_eq_pmf_map,
    cdf_pmf_map_eq_sum (binomialPMF n x)
      (fun k => standardizeBinomial n x ((k : ℕ) : ℝ)) Measurable.of_discrete]
""",
    """  rw [standardizedBinomialMeasure_eq_pmf_map, PMF.map_comp]
  rw [cdf_pmf_map_eq_sum (binomialPMF n x)
    (fun k => standardizeBinomial n x ((k : ℕ) : ℝ)) Measurable.of_discrete]
""",
    "discrete binomial CDF map normalization",
)
replace_once(
    discrete,
    """  apply Measure.eq_of_cdf
  funext t
""",
    """  apply Measure.eq_of_cdf _ _
  ext t
""",
    "discrete CDF extensionality",
)

runpy.run_path(".github/voronovskaja_migrate_round3.py", run_name="__main__")
