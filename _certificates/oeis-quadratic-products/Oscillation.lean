import RealPrimeLists
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.FieldSimp

/-!
# Prime-power oscillation in quadratic products

OEIS A363410 predicts oscillation at 2 and at primes congruent to 5 or 7
modulo 8. We specify the property by arbitrarily late nonzero terms
divisible by arbitrarily high powers of p and arbitrarily late terms
coprime to p. A norm criterion classifies this property for every d ≥ 2.
-/

namespace QuadraticDivisors

/-- The valuations are arbitrarily large on every tail, and zero on every tail. -/
def PrimePowerOscillation (d : ℤ) (p : ℕ) : Prop :=
  (∀ e N : ℕ, ∃ n : ℕ, N ≤ n ∧ B d n ≠ 0 ∧ (p : ℤ) ^ e ∣ B d n) ∧
  (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ¬ (p : ℤ) ∣ B d n)

private def normResidue (d : ℤ) (p n : ℕ) : ZMod p := (block d 1 n).norm

private theorem norm_coords (d : ℤ) (p n : ℕ) :
    normResidue d p n = (A d n : ZMod p) ^ 2 + d * (B d n : ZMod p) ^ 2 := by
  simp only [normResidue, Zsqrtd.norm_def, A, B, Int.cast_sub, Int.cast_mul, Int.cast_neg]
  ring

private theorem norm_step (d : ℤ) (p n : ℕ) :
    normResidue d p (n + 1) = normResidue d p n * (1 + d * ((n : ZMod p) + 1) ^ 2) := by
  simp only [normResidue, block, Zsqrtd.norm_mul, Int.cast_mul]
  congr 1
  simp [Zsqrtd.norm_def, factor]
  ring

private theorem coords_step (d : ℤ) (p n : ℕ) :
    (A d (n + 1) : ZMod p) =
      (A d n : ZMod p) - d * ((n : ZMod p) + 1) * (B d n : ZMod p) ∧
    (B d (n + 1) : ZMod p) =
      (B d n : ZMod p) + ((n : ZMod p) + 1) * (A d n : ZMod p) := by
  simp only [A, B, block, Zsqrtd.re_mul, Zsqrtd.im_mul, factor,
    Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  constructor <;> ring

private theorem high_powers (d : ℤ) (hd : 2 ≤ d) {p : ℕ} (hp : p.Prime) (e N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ B d n ≠ 0 ∧ (p : ℤ) ^ e ∣ B d n := by
  let m := p ^ e * (N + 1)
  have hpow : 0 < p ^ e := pow_pos hp.pos _
  have hlarge : N + 1 ≤ m := Nat.le_mul_of_pos_left _ hpow
  obtain ⟨hdiv, hnz⟩ := nonzero_multiple d hd m (by omega)
  refine ⟨2 * m, by omega, hnz, dvd_trans ?_ hdiv⟩
  exact ⟨(N : ℤ) + 1, by simp [m]⟩

private theorem units_on_every_tail (d : ℤ) (hd : 2 ≤ d) {p : ℕ} (hp : p.Prime)
    (hroot : ∀ r : ZMod p, 1 + d * r ^ 2 ≠ 0) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ¬ (p : ℤ) ∣ B d n := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hnorm (n : ℕ) : normResidue d p n ≠ 0 := by
    induction n with
    | zero => simp [normResidue, block]
    | succ n ih => rw [norm_step]; exact mul_ne_zero ih (hroot _)
  let m := p * (N + 1)
  have hlarge : N + 1 ≤ m := Nat.le_mul_of_pos_left _ hp.pos
  have hb : (B d (2 * m) : ZMod p) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    exact dvd_trans (show (p : ℤ) ∣ (m : ℤ) from ⟨N + 1, by simp [m]⟩)
      (nonzero_multiple d hd m (by omega)).1
  have ha : (A d (2 * m) : ZMod p) ≠ 0 := by
    intro h
    exact hnorm (2 * m) (by simp [norm_coords, h, hb])
  refine ⟨2 * m + 1, by omega, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, (coords_step d p (2 * m)).2, hb]
  simpa [m] using ha

/-- A root of the norm of a factor forces both coordinates to vanish modulo p
    from index 2p onward. -/
theorem eventual_zero_of_root (d : ℤ) (hd : 2 ≤ d) {p : ℕ} (hp : p.Prime)
    (r : ZMod p) (hr : 1 + d * r ^ 2 = 0) {n : ℕ} (hn : 2 * p ≤ n) :
    (A d n : ZMod p) = 0 ∧ (B d n : ZMod p) = 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hpos := hp.pos
  have hval := r.val_lt
  let k := r.val + p - 1
  have hk : k + 1 = r.val + p := by dsimp [k]; omega
  have hcast : (k : ZMod p) + 1 = r := by
    rw [← Nat.cast_one, ← Nat.cast_add, hk]
    simp
  have hz : normResidue d p (k + 1) = 0 := by rw [norm_step, hcast, hr, mul_zero]
  have later (j : ℕ) (hj : k + 1 ≤ j) : normResidue d p j = 0 := by
    induction j, hj using Nat.le_induction with
    | base => exact hz
    | succ j _ ih => rw [norm_step, ih, zero_mul]
  have hb : (B d (2 * p) : ZMod p) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (nonzero_multiple d hd p hp.pos).1
  have hnorm := later (2 * p) (by omega)
  rw [norm_coords, hb] at hnorm
  have ha : (A d (2 * p) : ZMod p) = 0 := by simpa using hnorm
  induction n, hn using Nat.le_induction with
  | base => exact ⟨ha, hb⟩
  | succ n _ ih =>
    rw [(coords_step d p n).1, (coords_step d p n).2, ih.1, ih.2]
    simp

/-- A complete finite-field criterion for oscillation in the imaginary coordinate. -/
theorem oscillation_iff (d : ℤ) (hd : 2 ≤ d) {p : ℕ} (hp : p.Prime) :
    PrimePowerOscillation d p ↔ ∀ r : ZMod p, 1 + d * r ^ 2 ≠ 0 := by
  constructor
  · intro h r hr
    obtain ⟨n, hn, hunit⟩ := h.2 (2 * p)
    exact hunit ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (eventual_zero_of_root d hd hp r hr hn).2)
  · exact fun h => ⟨high_powers d hd hp, units_on_every_tail d hd hp h⟩

private theorem root_iff_square {p : ℕ} [Fact p.Prime] {c : ZMod p} (hc : c ≠ 0) :
    (∃ r : ZMod p, 1 + c * r ^ 2 = 0) ↔ IsSquare (-c) := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨c * r, ?_⟩
    linear_combination (-c) * hr
  · rintro ⟨u, hu⟩
    refine ⟨u / c, ?_⟩
    field_simp [hc]
    linear_combination -hu

/-- The type-3 prediction of A363410 with an explicit meaning of oscillation. -/
theorem oscillation_A363410 {p : ℕ} (hp : p.Prime) :
    PrimePowerOscillation 2 p ↔ p = 2 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
  let _ : Fact p.Prime := ⟨hp⟩
  rw [oscillation_iff 2 (by decide) hp]
  by_cases htwo : p = 2
  · subst p
    constructor
    · exact fun _ => Or.inl rfl
    · intro _ r
      change 1 + (2 : ZMod 2) * r ^ 2 ≠ 0
      rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul, add_zero]
      exact one_ne_zero
  · have hc : (2 : ZMod p) ≠ 0 := by
      intro hz
      have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hz
      exact (Nat.dvd_prime Nat.prime_two).mp hdiv |>.elim hp.ne_one htwo
    simp only [Int.cast_ofNat]
    rw [← not_exists, root_iff_square hc, ZMod.exists_sq_eq_neg_two_iff htwo]
    have hodd := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr htwo
    omega

end QuadraticDivisors

#print axioms QuadraticDivisors.eventual_zero_of_root
#print axioms QuadraticDivisors.oscillation_iff
#print axioms QuadraticDivisors.oscillation_A363410
