import FormalConjectures.Wikipedia.LanderParkinAndSelfridgeConjecture

/-!
# Counterexample to the literal Lander–Parkin–Selfridge declaration

The catalog theorem quantifies over all natural numbers `n` and `m`, although its
prose requires positive numbers of summands. Taking both index types to be empty
makes the two power sums equal, while `k = 1` makes the claimed bound false.
-/

namespace LanderParkinSelfridge

/-- The catalog declaration is false because it permits two empty sums. -/
@[category research solved, AMS 11]
theorem lander_parkin_selfridge_false :
    ¬ (∀ (k n m : ℕ) (x : Fin n → ℕ) (y : Fin m → ℕ),
      (∀ i, 0 < x i) → (∀ j, 0 < y j) →
      (∀ i j, x i ≠ y j) →
      ∑ i, x i ^ k = ∑ j, y j ^ k →
      k ≤ n + m) := by
  intro h
  have hbad : (1 : ℕ) ≤ 0 + 0 :=
    h 1 0 0
      (fun i => Fin.elim0 i)
      (fun j => Fin.elim0 j)
      (by intro i; exact Fin.elim0 i)
      (by intro j; exact Fin.elim0 j)
      (by intro i; exact Fin.elim0 i)
      (by simp)
  omega

#print axioms lander_parkin_selfridge_false

end LanderParkinSelfridge
