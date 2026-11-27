import Mathlib
import Cramer.Main
import Main

/-!
# Erdős 462 with the external Cramér and RH proofs

The sum includes prime integers. This is the statement recorded in Formal Conjectures at
`f606af160664c5a10952e9a957b100a1cd45bbeb`. The witnesses in the proof are both one.

Lean 4.36.0 dependency revisions:

* senamakel/cramer-rh: fb22f0a8535130c32d6175bc314062334923629b
* leanprover-community/riemann-hypothesis: 507a75d91d131d627b380df4e32f6e9fb21dd067

With those projects built, run from the Cramér checkout:

```sh
abs_lean_path() {
  lake env python3 -c 'import os; print(os.pathsep.join(os.path.abspath(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p))'
}
cramer_path=$(abs_lean_path)
rh_path=$(cd "$RH_DIR" && abs_lean_path)
lean_bin=$(lake env which lean)
LEAN_PATH="$cramer_path:$rh_path" "$lean_bin" "$PROOF_FILE"
```

Upstream’s
`scripts/check-unconditional.sh` documents its combined build. Its verification report
gives the axiom audit for the interval theorem used here.
-/

open Filter

theorem Erdos462.from_interval
    (interval : ∀ x : ℝ, 2 ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧
      (p : ℝ) ≤ x + 2 * Real.sqrt x * Real.log x) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      c ≤ ∑ n ∈ Finset.Icc x ⌊(x : ℝ) + C * Real.sqrt x * (Real.log x) ^ 2⌋₊,
        (n.minFac : ℝ) / n := by
  refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
  have hlog : ∀ᶠ x : ℕ in atTop, 2 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop 2, hlog] with x hx hlogx
  obtain ⟨p, hp, hxp, hpx⟩ := interval x (by exact_mod_cast hx)
  have hwidth : 2 * Real.log x ≤ (Real.log x) ^ 2 := by nlinarith
  have hmem : p ∈ Finset.Icc x ⌊(x : ℝ) + 1 * Real.sqrt x * (Real.log x) ^ 2⌋₊ := by
    refine Finset.mem_Icc.mpr ⟨by exact_mod_cast hxp.le, Nat.le_floor ?_⟩
    linarith [mul_le_mul_of_nonneg_left hwidth (Real.sqrt_nonneg (x : ℝ))]
  calc
    (1 : ℝ) = (p.minFac : ℝ) / p := by simp [hp.minFac_eq, hp.ne_zero]
    _ ≤ _ := Finset.single_le_sum (f := fun n : ℕ => (n.minFac : ℝ) / n)
      (fun _ _ => by positivity) hmem

theorem Erdos462.erdos_462 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      c ≤ ∑ n ∈ Finset.Icc x ⌊(x : ℝ) + C * Real.sqrt x * (Real.log x) ^ 2⌋₊,
        (n.minFac : ℝ) / n :=
  Erdos462.from_interval (Cramer.primeInShortInterval_of_RH riemannHypothesis)

#print axioms Erdos462.erdos_462
