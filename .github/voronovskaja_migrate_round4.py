from pathlib import Path


def replace_once(path: Path, old: str, new: str, label: str) -> None:
    text = path.read_text()
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected one occurrence, found {count}")
    path.write_text(text.replace(old, new, 1))


discrete = Path("FormalConjectures/Paper/VoronovskajaDiscreteLaw.lean")
replace_once(
    discrete,
    """        _ = ENNReal.ofReal 1 := by
          congr 1
          simpa only [Fin.sum_univ_eq_sum_range] using
            sum_bezierWeight n hα (x : ℝ)
""",
    """        _ = ENNReal.ofReal 1 := by
          congr 1
          have hsum :
              (∑ k : Fin (n + 1), bezierWeight n (k : ℕ) α (x : ℝ)) =
                ∑ k ∈ Finset.range (n + 1), bezierWeight n k α (x : ℝ) := by
            simpa using (Fin.sum_univ_eq_sum_range
              (f := fun k : ℕ => bezierWeight n k α (x : ℝ)))
          rw [hsum]
          exact sum_bezierWeight n hα (x : ℝ)
""",
    "Bezier PMF Fin-to-range sum",
)
replace_once(
    discrete,
    """  · rw [cdf_standardizedBinomialMeasure_eq_sum]
    change (∑ k : Fin (n + 1),
      if P k then (bernsteinPolynomial ℝ n k).eval (x : ℝ) else 0) = _
    simpa only [Fin.sum_univ_eq_sum_range, ← Finset.sum_filter, hfilter] using
      sum_bernsteinPolynomial_range n m hm (x : ℝ)
""",
    """  · rw [cdf_standardizedBinomialMeasure_eq_sum]
    change (∑ k : Fin (n + 1),
      if P k then (bernsteinPolynomial ℝ n k).eval (x : ℝ) else 0) = _
    have hsum :
        (∑ k : Fin (n + 1),
          if P k then (bernsteinPolynomial ℝ n k).eval (x : ℝ) else 0) =
        ∑ k ∈ Finset.range (n + 1),
          if P k then (bernsteinPolynomial ℝ n k).eval (x : ℝ) else 0 := by
      simpa using (Fin.sum_univ_eq_sum_range
        (f := fun k : ℕ =>
          if P k then (bernsteinPolynomial ℝ n k).eval (x : ℝ) else 0))
    rw [hsum, ← Finset.sum_filter, hfilter]
    exact sum_bernsteinPolynomial_range n m hm (x : ℝ)
""",
    "binomial cutoff Fin-to-range sum",
)
replace_once(
    discrete,
    """  · intro α hα
    rw [cdf_standardizedBezierMeasure_eq_sum]
    change (∑ k : Fin (n + 1), if P k then bezierWeight n k α (x : ℝ) else 0) = _
    simpa only [Fin.sum_univ_eq_sum_range, ← Finset.sum_filter, hfilter] using
      sum_bezierWeight_range n m α (x : ℝ)
""",
    """  · intro α hα
    rw [cdf_standardizedBezierMeasure_eq_sum]
    change (∑ k : Fin (n + 1), if P k then bezierWeight n k α (x : ℝ) else 0) = _
    have hsum :
        (∑ k : Fin (n + 1), if P k then bezierWeight n k α (x : ℝ) else 0) =
        ∑ k ∈ Finset.range (n + 1), if P k then bezierWeight n k α (x : ℝ) else 0 := by
      simpa using (Fin.sum_univ_eq_sum_range
        (f := fun k : ℕ => if P k then bezierWeight n k α (x : ℝ) else 0))
    rw [hsum, ← Finset.sum_filter, hfilter]
    exact sum_bezierWeight_range n m α (x : ℝ)
""",
    "Bezier cutoff Fin-to-range sum",
)
