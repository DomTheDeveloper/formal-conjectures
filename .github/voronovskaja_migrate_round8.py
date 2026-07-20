from pathlib import Path


def replace_once(path: Path, old: str, new: str, label: str) -> None:
    text = path.read_text()
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected one occurrence, found {count}")
    path.write_text(text.replace(old, new, 1))


path = Path("FormalConjectures/Paper/VoronovskajaSecondMoment.lean")
replace_once(
    path,
    """  rw [integral_sq_standardizedBezierMeasure_eq_sum]
  rw [Fin.sum_univ_eq_sum_range]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
""",
    """  rw [integral_sq_standardizedBezierMeasure_eq_sum]
  have hsum :
      (∑ k : Fin (n + 1),
        bezierWeight n (k : ℕ) α (x : ℝ) *
          standardizeBinomial n x ((k : ℕ) : ℝ) ^ 2) =
        ∑ k ∈ Finset.range (n + 1),
          bezierWeight n k α (x : ℝ) *
            standardizeBinomial n x (k : ℝ) ^ 2 := by
    simpa using (Fin.sum_univ_eq_sum_range
      (f := fun k : ℕ =>
        bezierWeight n k α (x : ℝ) *
          standardizeBinomial n x (k : ℝ) ^ 2) (n + 1))
  rw [hsum]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
""",
    "second-moment Fin-to-range sum",
)
replace_once(
    path,
    """  field_simp [hnR, hsqrt, hsd]
  rw [Real.sq_sqrt]
  · ring
  · positivity
""",
    """  field_simp [hnR, hsqrt, hsd]
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrt_four : Real.sqrt (n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
    calc
      Real.sqrt (n : ℝ) ^ 4 = (Real.sqrt (n : ℝ) ^ 2) ^ 2 := by ring
      _ = (n : ℝ) ^ 2 := by rw [hsqrt_sq]
  rw [hsqrt_four]
""",
    "second-moment terminal square-root normalization",
)
