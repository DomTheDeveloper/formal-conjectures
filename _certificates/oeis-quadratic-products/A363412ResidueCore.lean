import Init

namespace A363412Core

/-- Real and imaginary coefficients of the defining product in Z[sqrt(-3)]. -/
def coord : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 =>
    let (a, b) := coord n
    (a - 3 * ((n : Int) + 1) * b, b + ((n : Int) + 1) * a)

private theorem residues (n : Nat) :
    (coord n).1 % 3 = 1 ∧ (2 * (coord n).2) % 3 =
    (((n : Int) % 3) * (((n : Int) % 3) + 1)) % 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨ha, hb⟩ := ih
    simp only [coord, Int.natCast_succ]
    constructor
    · rw [Int.mul_assoc (3 : Int)]
      omega
    · have hn : (n : Int) % 3 = 0 ∨ (n : Int) % 3 = 1 ∨ (n : Int) % 3 = 2 := by omega
      rw [Int.mul_add, Int.add_emod, hb,
        show 2 * ((↑n + 1) * (coord n).1) = (2 * (↑n + 1)) * (coord n).1 by
          rw [Int.mul_assoc]]
      rw [Int.mul_emod (2 * ((n : Int)+1)) (coord n).1, ha, Int.mul_one]
      rcases hn with h | h | h
      · rw [h, show ((n:Int)+1)%3 = 1 by omega]
        omega
      · rw [h, show ((n:Int)+1)%3 = 2 by omega]
        omega
      · rw [h, show ((n:Int)+1)%3 = 0 by omega]
        omega

theorem three_not_dvd (n : Nat) : ¬ (3 : Int) ∣ (coord (3*n+1)).2 := by
  have h := (residues (3*n+1)).2
  have hm : ((3*n+1 : Nat) : Int) % 3 = 1 := by omega
  rw [hm] at h
  omega

end A363412Core
#print axioms A363412Core.three_not_dvd
