import Oscillation

/-!
# Solutions stated using the finite products in the OEIS

These declarations specialize the general theorems to the source sequences.
The two coordinates of an element of ℤ[√(-d)] are its real part and its
imaginary part divided by √d under the complex embedding.
-/

namespace QuadraticDivisors.Oeis

/-- The real coordinate of the finite product through n. -/
def realTerm (d : ℤ) (n : ℕ) : ℤ :=
  (∏ k ∈ Finset.range n, (⟨1, 1 + (k : ℤ)⟩ : Zsqrtd (-d))).re

/-- The coefficient of √(-d) in the finite product through n. -/
def imagTerm (d : ℤ) (n : ℕ) : ℤ :=
  (∏ k ∈ Finset.range n, (⟨1, 1 + (k : ℤ)⟩ : Zsqrtd (-d))).im

private theorem real_eq (d : ℤ) (n : ℕ) : realTerm d n = A d n := by
  rw [A, block_eq_prod]
  rfl

private theorem imag_eq (d : ℤ) (n : ℕ) : imagTerm d n = B d n := by
  rw [B, block_eq_prod]
  rfl

/-- A363415. The exact prime prefix for the product with d = 5. -/
theorem corrected_A363415 {p : ℕ} (hp : p.Prime) (hb : p ≤ 197) :
    (∀ n, ¬ (p : ℤ) ∣ realTerm 5 n) ↔
      p ∈ ([5, 11, 13, 31, 53, 79, 97, 113, 137, 139, 157, 179, 193, 197] : List ℕ) := by
  simp only [real_eq]
  rw [← corrected_prefix_A363415, mem_primePrefix_iff 5 (by decide)]
  simp [hp, hb]

/-- A363410. Every prime divides a nonzero term. -/
theorem prime_divisors_A363410 {p : ℕ} (hp : p.Prime) :
    ∃ n : ℕ, imagTerm 2 n ≠ 0 ∧ (p : ℤ) ∣ imagTerm 2 n := by
  obtain ⟨n, _, hn, hdiv⟩ := prime_divides_some_term 2 (by decide) p hp
  exact ⟨n, by simpa only [imag_eq] using And.intro hn hdiv⟩

/-- A363410. Each tail has units and arbitrarily high prime powers exactly
    at 2 and at primes congruent to 5 or 7 modulo 8. -/
theorem oscillating_primes_A363410 {p : ℕ} (hp : p.Prime) :
    ((∀ e N : ℕ, ∃ n : ℕ, N ≤ n ∧ imagTerm 2 n ≠ 0 ∧ (p : ℤ) ^ e ∣ imagTerm 2 n) ∧
      (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ¬ (p : ℤ) ∣ imagTerm 2 n)) ↔
        p = 2 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
  simpa only [imag_eq, PrimePowerOscillation] using oscillation_A363410 hp

end QuadraticDivisors.Oeis

#print axioms QuadraticDivisors.Oeis.corrected_A363415
#print axioms QuadraticDivisors.Oeis.prime_divisors_A363410
#print axioms QuadraticDivisors.Oeis.oscillating_primes_A363410
