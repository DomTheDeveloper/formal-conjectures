import Init

/-! A dependency-free certificate for the cubic lattice coordination numbers.
The coefficient of x^d in ((1+x)/(1-x))^h satisfies the recurrence below,
by multiplying two successive generating functions by 1-x and 1+x. -/

namespace CubicLattice

/-- Row zero is the origin. Each new coordinate gives the Delannoy recurrence. -/
def sphere : Nat → Nat → Nat
  | 0 => fun d => if d = 0 then 1 else 0
  | h + 1 => fun d => Nat.rec 1 (fun j previous => sphere h (j+1) + previous + sphere h j) d

@[simp] theorem distance_zero (h : Nat) : sphere h 0 = 1 := by cases h <;> rfl
@[simp] theorem dimension_zero (d : Nat) : sphere 0 (d+1) = 0 := rfl
theorem next (h d : Nat) :
    sphere (h+1) (d+1) = sphere h (d+1) + sphere (h+1) d + sphere h d := rfl

/-- At any positive distance the count is twice the dimension modulo four. -/
theorem mod_four (h d : Nat) : sphere h (d+1) % 4 = (2*h) % 4 := by
  induction h generalizing d with
  | zero => simp
  | succ h ih =>
    induction d with
    | zero =>
      rw [next, distance_zero, distance_zero]
      have base := ih 0
      omega
    | succ d hd =>
      rw [next]
      have h1 := ih (d+1)
      have h2 := ih d
      omega

/-- In every odd dimension the count has exactly one factor of two. -/
theorem odd_dimension (h d : Nat) : sphere (2*h+1) (d+1) % 4 = 2 := by
  rw [mod_four]
  omega

/-- In two dimensions the count is exactly four times the positive distance. -/
theorem two_dimensional (d : Nat) : sphere 2 (d+1) = 4 * (d+1) := by
  have one (k : Nat) : sphere 1 (k+1) = 2 := by
    induction k with
    | zero => rfl
    | succ k hk =>
      rw [show 1 = 0+1 by rfl, next]
      simp [hk]
  induction d with
  | zero => rfl
  | succ d hd =>
    change sphere (1+1) (d+1+1) = _
    rw [next, one, hd, one]
    omega

/-- Closed form in dimension three at every positive radius. -/
theorem three_dimensional (d : Nat) : sphere 3 (d+1) = 4*(d+1)^2 + 2 := by
  induction d with
  | zero => rfl
  | succ d hd =>
    change sphere (2+1) (d+1+1) = _
    rw [next, two_dimensional, hd, two_dimensional]
    simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul] <;> omega

/-- A division-free closed form in dimension four at every positive radius. -/
theorem four_dimensional (d : Nat) : 3*sphere 4 (d+1) = 8*(d+1)*((d+1)^2+2) := by
  induction d with
  | zero => rfl
  | succ d hd =>
    change 3*sphere (3+1) (d+1+1) = _
    rw [next, three_dimensional, three_dimensional, Nat.mul_add, Nat.mul_add, hd]
    simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc] <;> omega

#print axioms four_dimensional
#print axioms mod_four
#print axioms odd_dimension
#print axioms two_dimensional

end CubicLattice
