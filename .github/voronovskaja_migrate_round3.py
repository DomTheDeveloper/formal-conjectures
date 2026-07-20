from pathlib import Path


def replace_once(path: Path, old: str, new: str, label: str) -> None:
    text = path.read_text()
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected one occurrence, found {count}")
    path.write_text(text.replace(old, new, 1))


proof = Path("FormalConjectures/Paper/VoronovskajaProof.lean")
replace_once(
    proof,
    "noncomputable def bezierWeight (n k : ℕ) (α x : ℝ) : ℝ :=\n",
    "@[expose]\nnoncomputable def bezierWeight (n k : ℕ) (α x : ℝ) : ℝ :=\n",
    "expose Bezier weight",
)

moments = Path(
    "FormalConjecturesForMathlib/Probability/Distributions/PoweredBinomialMoments.lean"
)
replace_once(
    moments,
    """      have hq1 : q ≤ 1 := by
        dsimp [q]
        rw [exp_le_one_iff]
        have hfrac : 0 ≤ t ^ 2 / (2 * c) := by positivity
        linarith
""",
    """      have hq1 : q ≤ 1 := by
        dsimp [q]
        exact exp_le_one_iff.mpr (by
          have hfrac : 0 ≤ t ^ 2 / (2 * c) := by positivity
          simpa [neg_div] using neg_nonpos.mpr hfrac)
""",
    "moments direct exponential upper bound",
)

second = Path(
    "FormalConjecturesForMathlib/Probability/Distributions/PoweredBinomialSecondMoment.lean"
)
replace_once(
    second,
    """  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [exp_le_one_iff]
    have hfrac : 0 ≤ t / (2 * c) := by positivity
    linarith
""",
    """  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact exp_le_one_iff.mpr (by
      have hfrac : 0 ≤ t / (2 * c) := by positivity
      simpa [neg_div] using neg_nonpos.mpr hfrac)
""",
    "second direct exponential upper bound",
)


discrete = Path("FormalConjectures/Paper/VoronovskajaDiscreteLaw.lean")
replace_once(
    discrete,
    """noncomputable def standardizedBezierPMF
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) : PMF ℝ :=
  (bezierPMF n α hα x).map
    (fun k => standardizeBinomial n x ((k : ℕ) : ℝ))
""",
    """noncomputable def standardizedBezierPMF
    (n : ℕ) (α : ℝ) (hα : 0 < α) (x : I) : PMF ℝ :=
  (bezierPMF n α hα x).map
    (fun k : Fin (n + 1) => standardizeBinomial n x ((k : ℕ) : ℝ))
""",
    "explicit Bezier PMF index type",
)
replace_once(
    discrete,
    """        _ = ENNReal.ofReal 1 := by
          congr 1
          rw [← Fin.sum_univ_eq_sum_range]
          exact sum_bezierWeight n hα (x : ℝ)
""",
    """        _ = ENNReal.ofReal 1 := by
          congr 1
          simpa only [Fin.sum_univ_eq_sum_range] using
            sum_bezierWeight n hα (x : ℝ)
""",
    "Bezier PMF total mass",
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
  change (binomialPMF n x).toMeasure.map
      (fun k : Fin (n + 1) => standardizeBinomial n x ((k : ℕ) : ℝ)) =
    ((binomialPMF n x).map
      (fun k : Fin (n + 1) => standardizeBinomial n x ((k : ℕ) : ℝ))).toMeasure
  exact PMF.toMeasure_map
    (fun k : Fin (n + 1) => standardizeBinomial n x ((k : ℕ) : ℝ))
    (binomialPMF n x) Measurable.of_discrete
""",
    """private theorem standardizedBinomialMeasure_eq_pmf_map
    (n : ℕ) (x : I) :
    standardizedBinomialMeasure n x =
      ((binomialPMF n x).map
        (fun k : Fin (n + 1) => standardizeBinomial n x ((k : ℕ) : ℝ))).toMeasure := by
  have hcast : Measurable (fun k : Fin (n + 1) ↦ (k : ℝ)) := .of_discrete
  have hstd : Measurable (standardizeBinomial n x) :=
    (continuous_standardizeBinomial n x).measurable
  rw [standardizedBinomialMeasure, binomialRealMeasure]
  rw [Measure.map_map hstd hcast]
  simpa [Function.comp_def] using
    (PMF.toMeasure_map
      (fun k : Fin (n + 1) => standardizeBinomial n x ((k : ℕ) : ℝ))
      (binomialPMF n x) Measurable.of_discrete)
""",
    "standardized binomial PMF map",
)
replace_once(
    discrete,
    """  rw [standardizedBezierMeasure, standardizedBezierPMF, PMF.map_comp]
  rw [cdf_pmf_map_eq_sum (bezierPMF n α hα x)
    (fun k => standardizeBinomial n x ((k : ℕ) : ℝ)) Measurable.of_discrete]
""",
    """  rw [standardizedBezierMeasure, standardizedBezierPMF]
  rw [cdf_pmf_map_eq_sum (bezierPMF n α hα x)
    (fun k : Fin (n + 1) => standardizeBinomial n x ((k : ℕ) : ℝ))
    Measurable.of_discrete]
""",
    "Bezier CDF direct PMF map",
)
replace_once(
    discrete,
    """  rw [standardizedBinomialMeasure_eq_pmf_map, PMF.map_comp]
  rw [cdf_pmf_map_eq_sum (binomialPMF n x)
    (fun k => standardizeBinomial n x ((k : ℕ) : ℝ)) Measurable.of_discrete]
""",
    """  rw [standardizedBinomialMeasure_eq_pmf_map]
  rw [cdf_pmf_map_eq_sum (binomialPMF n x)
    (fun k : Fin (n + 1) => standardizeBinomial n x ((k : ℕ) : ℝ))
    Measurable.of_discrete]
""",
    "binomial CDF direct PMF map",
)
replace_once(
    discrete,
    """  · rw [cdf_standardizedBinomialMeasure_eq_sum]
    change (∑ k : Fin (n + 1),
      if P k then (bernsteinPolynomial ℝ n k).eval (x : ℝ) else 0) = _
    rw [← Fin.sum_univ_eq_sum_range]
    rw [← Finset.sum_filter]
    rw [hfilter]
    exact sum_bernsteinPolynomial_range n m hm (x : ℝ)
""",
    """  · rw [cdf_standardizedBinomialMeasure_eq_sum]
    change (∑ k : Fin (n + 1),
      if P k then (bernsteinPolynomial ℝ n k).eval (x : ℝ) else 0) = _
    simpa only [Fin.sum_univ_eq_sum_range, ← Finset.sum_filter, hfilter] using
      sum_bernsteinPolynomial_range n m hm (x : ℝ)
""",
    "binomial cutoff finite sum",
)
replace_once(
    discrete,
    """  · intro α hα
    rw [cdf_standardizedBezierMeasure_eq_sum]
    change (∑ k : Fin (n + 1), if P k then bezierWeight n k α (x : ℝ) else 0) = _
    rw [← Fin.sum_univ_eq_sum_range]
    rw [← Finset.sum_filter]
    rw [hfilter]
    exact sum_bezierWeight_range n m α (x : ℝ)
""",
    """  · intro α hα
    rw [cdf_standardizedBezierMeasure_eq_sum]
    change (∑ k : Fin (n + 1), if P k then bezierWeight n k α (x : ℝ) else 0) = _
    simpa only [Fin.sum_univ_eq_sum_range, ← Finset.sum_filter, hfilter] using
      sum_bezierWeight_range n m α (x : ℝ)
""",
    "Bezier cutoff finite sum",
)
replace_once(
    discrete,
    """  simp only [poweredStandardizedBinomialProbability, poweredProbability,
    ProbabilityMeasure.coe_mk, cdf_poweredMeasure, poweredCDF_apply]
""",
    """  simp only [poweredStandardizedBinomialProbability, poweredProbability,
    standardizedBinomialProbability, ProbabilityMeasure.coe_mk,
    cdf_poweredMeasure, poweredCDF_apply]
""",
    "final CDF wrapper normalization",
)
