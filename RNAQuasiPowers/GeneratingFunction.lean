import RNAQuasiPowers.Radicand

namespace RNAQuasiPowers

/-!
# Recursive grammar and algebraic discriminant

Let `G(t,x,z)` count all RNA secondary structures, including the empty
structure and the one-base structure.  Decomposing at the first base gives

`G = 1 + tG + t² z ((G - 1) + (x - 1)t/(1-t)) G`.

The term `(G - 1)` forces a nonempty interior of a basepair, and the correction
`(x - 1)t/(1-t)` marks a basepair as a hairpin exactly when its interior is a
nonempty sequence of unpaired bases.

After clearing `1-t`, this is a quadratic equation in `G`.  This file proves
that its discriminant is exactly the radicand used in the paper.
-/

/-- Right-hand side of the recursive grammar. -/
def grammarRhs (t x z g : Real) : Real :=
  1 + t * g + t ^ 2 * z * (g - 1 + (x - 1) * t / (1 - t)) * g

/-- Leading coefficient of the cleared quadratic equation. -/
def grammarA (t z : Real) : Real := t ^ 2 * z * (1 - t)

/-- Linear coefficient of the cleared quadratic equation. -/
def grammarB (t x z : Real) : Real :=
  t ^ 2 * z * (x * t - 1) - (1 - t) ^ 2

/-- Constant coefficient of the cleared quadratic equation. -/
def grammarC (t : Real) : Real := 1 - t

/-- The cleared quadratic residual. -/
def grammarResidual (t x z g : Real) : Real :=
  grammarA t z * g ^ 2 + grammarB t x z * g + grammarC t

/-- Clearing the geometric-series denominator yields the quadratic residual. -/
theorem grammar_clearing_identity (t x z g : Real) (ht : t ≠ 1) :
    (1 - t) * (grammarRhs t x z g - g) = grammarResidual t x z g := by
  have hden : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  unfold grammarRhs grammarResidual grammarA grammarB grammarC
  field_simp [hden]
  ring

/-- Away from `t=1`, the recursive grammar is equivalent to the quadratic. -/
theorem grammar_equation_iff (t x z g : Real) (ht : t ≠ 1) :
    g = grammarRhs t x z g ↔ grammarResidual t x z g = 0 := by
  have hid := grammar_clearing_identity t x z g ht
  have hden : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  constructor
  · intro h
    rw [← h, sub_self, mul_zero] at hid
    exact hid.symm
  · intro h
    rw [h] at hid
    have hz : grammarRhs t x z g - g = 0 := by
      exact (mul_eq_zero.mp hid).resolve_left hden
    linarith

/-- The quadratic discriminant produced by the grammar. -/
def grammarDiscriminant (t x z : Real) : Real :=
  grammarB t x z ^ 2 - 4 * grammarA t z * grammarC t

/-- The grammar gives exactly the radicand printed by Bu--Kauers--Zeilberger. -/
theorem grammar_discriminant_eq_radicand (t x z : Real) :
    grammarDiscriminant t x z = radicand t x z := by
  unfold grammarDiscriminant grammarA grammarB grammarC radicand
  ring

end RNAQuasiPowers
