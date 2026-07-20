from pathlib import Path
import runpy


def replace_once(path: Path, old: str, new: str, label: str) -> None:
    text = path.read_text()
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected one occurrence, found {count}")
    path.write_text(text.replace(old, new, 1))


proof = Path("FormalConjectures/Paper/VoronovskajaProof.lean")
replace_once(
    proof,
    """noncomputable def bezierCenteredMoment (n : ℕ) (α x : ℝ) : ℝ :=
""",
    """@[expose]
noncomputable def bezierCenteredMoment (n : ℕ) (α x : ℝ) : ℝ :=
""",
    "expose centered Bezier moment",
)
replace_once(
    proof,
    """noncomputable def bezierTaylorRemainder
""",
    """@[expose]
noncomputable def bezierTaylorRemainder
""",
    "expose Bezier Taylor remainder",
)

discrete = Path("FormalConjectures/Paper/VoronovskajaDiscreteLaw.lean")
replace_once(
    discrete,
    """/-!
# The discrete probability law of Bézier--Bernstein weights
""",
    """public section

/-!
# The discrete probability law of Bézier--Bernstein weights
""",
    "export discrete-law declarations",
)
replace_once(
    discrete,
    """noncomputable def standardizedBezierPMF
""",
    """@[expose]
noncomputable def standardizedBezierPMF
""",
    "expose standardized Bezier PMF",
)
replace_once(
    discrete,
    """noncomputable def standardizedBezierMeasure
""",
    """@[expose]
noncomputable def standardizedBezierMeasure
""",
    "expose standardized Bezier measure",
)

expectation = Path("FormalConjectures/Paper/VoronovskajaExpectation.lean")
replace_once(
    expectation,
    """    · exact (ht.not_lt h).elim
""",
    """    · exact (lt_asymm ht h).elim
""",
    "expectation positive threshold contradiction",
)
replace_once(
    expectation,
    """    _ =
        (∫ t in Ioi 0, μ.real {z : ℝ | t < (Real.toNNReal z : ℝ)}) -
          ∫ t in Ioi 0, μ.real {z : ℝ | t ≤ (Real.toNNReal (-z) : ℝ)} := by
      rw [(hid.real_toNNReal).integral_eq_integral_meas_lt
          (Eventually.of_forall fun z ↦ by positivity)]
      rw [(hid.neg.real_toNNReal).integral_eq_integral_meas_le
          (Eventually.of_forall fun z ↦ by positivity)]
""",
    """    _ =
        (∫ t in Ioi 0, μ.real {z : ℝ | t < (Real.toNNReal z : ℝ)}) -
          ∫ t in Ioi 0, μ.real {z : ℝ | t ≤ (Real.toNNReal (-z) : ℝ)} := by
      have hposLayer :
          (∫ z : ℝ, (Real.toNNReal z : ℝ) ∂μ) =
            ∫ t in Ioi 0, μ.real {z : ℝ | t < (Real.toNNReal z : ℝ)} := by
        simpa using
          (hid.real_toNNReal).integral_eq_integral_meas_lt
            (Eventually.of_forall fun z ↦ by positivity)
      have hnegLayer :
          (∫ z : ℝ, (Real.toNNReal (-z) : ℝ) ∂μ) =
            ∫ t in Ioi 0, μ.real {z : ℝ | t ≤ (Real.toNNReal (-z) : ℝ)} := by
        simpa only [Pi.neg_apply] using
          (hid.neg.real_toNNReal).integral_eq_integral_meas_le
            (Eventually.of_forall fun z ↦ by positivity)
      rw [hposLayer, hnegLayer]
""",
    "expectation layer-cake normalization",
)

runpy.run_path(".github/voronovskaja_migrate_round7.py", run_name="__main__")
