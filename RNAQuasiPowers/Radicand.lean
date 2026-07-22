import Mathlib

namespace RNAQuasiPowers

/--
The radicand in the algebraic generating function from Bu--Kauers--Zeilberger.
The variables are `t` (size), `x` (hairpins), and `z` (basepairs).
-/
def radicand (t x z : Real) : Real :=
  t ^ 6 * x ^ 2 * z ^ 2
    - 2 * t ^ 5 * x * z ^ 2
    - 2 * t ^ 5 * x * z
    + 4 * t ^ 4 * x * z
    + t ^ 4 * z ^ 2
    - 2 * t ^ 4 * z
    - 2 * t ^ 3 * x * z
    + t ^ 4
    + 4 * t ^ 3 * z
    - 4 * t ^ 3
    - 2 * t ^ 2 * z
    + 6 * t ^ 2
    - 4 * t
    + 1

/-- At the unmarked point `x = z = 1`, the radicand factors completely. -/
theorem radicand_at_one_factor (t : Real) :
    radicand t 1 1 =
      (t - 1) ^ 2 * (t ^ 2 - 3 * t + 1) * (t ^ 2 + t + 1) := by
  unfold radicand
  ring

/-- The formal derivative in `t` of `radicand t 1 1`. -/
def dRadicandAtOne (t : Real) : Real :=
  6 * t ^ 5 - 20 * t ^ 4 + 16 * t ^ 3 - 6 * t ^ 2 + 8 * t - 4

/-- Polynomial division by the quadratic factor. -/
theorem dRadicandAtOne_reduction (t : Real) :
    dRadicandAtOne t =
      (6 * t ^ 3 - 2 * t ^ 2 + 4 * t + 8) * (t ^ 2 - 3 * t + 1)
        + (28 * t - 12) := by
  unfold dRadicandAtOne
  ring

end RNAQuasiPowers
