# Moment-limit finite-sum verification trigger.
from pathlib import Path
import runpy


def replace_once(path: Path, old: str, new: str, label: str) -> None:
    text = path.read_text()
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected one occurrence, found {count}")
    path.write_text(text.replace(old, new, 1))


path = Path(
    "FormalConjecturesForMathlib/Probability/Distributions/PoweredBinomialTailIntegrability.lean"
)

replace_once(
    path,
    """  rw [standardizedBernoulliSubgaussianParameter]
  simp only [hwidth]
  positivity
""",
    """  rw [standardizedBernoulliSubgaussianParameter]
  simp only [hwidth]
  have hinv : 0 < 1 / bernoulliStdDev p := one_div_pos.mpr hs
  have hnormNN : 0 < ‖(1 / bernoulliStdDev p : ℝ)‖₊ := by
    exact_mod_cast (norm_pos_iff.mpr (one_div_ne_zero (ne_of_gt hs)))
  positivity
""",
    "tail-integrability parameter positivity",
)

replace_once(
    path,
    """private lemma exp_rpow_tail_eq'
    {c α t : ℝ} (hc : c ≠ 0) :
    (exp (-t ^ 2 / (2 * c))) ^ α =
      exp (-(α / (2 * c)) * t ^ 2) := by
  rw [← Real.exp_mul]
  congr 1
  field_simp [hc]
  ring
""",
    """private lemma exp_rpow_tail_eq'
    {c α t : ℝ} (hc : c ≠ 0) :
    (exp (-t ^ 2 / (2 * c))) ^ α =
      exp (-(α / (2 * c)) * t ^ 2) := by
  rw [← Real.exp_mul]
  congr 1
  field_simp [hc]
""",
    "tail-integrability powered exponential identity",
)

replace_once(
    path,
    """    have heq : exp (-t ^ 2 / (2 * c)) = exp (-b * t ^ 2) := by
      congr 1
      field_simp [hc0]
      ring
""",
    """    have heq : exp (-t ^ 2 / (2 * c)) = exp (-b * t ^ 2) := by
      congr 1
      dsimp [b]
      field_simp [hc0]
""",
    "tail-integrability alpha-ge-one exponential identity",
)

runpy.run_path(".github/voronovskaja_migrate_round6.py", run_name="__main__")
