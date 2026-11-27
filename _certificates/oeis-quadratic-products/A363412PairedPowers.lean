import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Coprime.Lemmas

/-! The paired-valuation claim also has an earlier formal proof in the Omega
Institute's trureturing project: https://www.trureturing.org/research/bala3634-paired-valuations/ .
Here divisibility by every power is proved using nested quadratic-product blocks. -/

namespace A363412

/-- Multiply by 1 + k√(-3) in integer coordinates. -/
def push (k : ℤ) (x : ℤ × ℤ) : ℤ × ℤ := (x.1-3*k*x.2, x.2+k*x.1)

/-- The product of the h successive factors starting at index a. -/
def block (a : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1,0)
  | h+1 => push a (block (a+1) h)

def term (n : ℕ) : ℤ := (block 1 n).2

private theorem commute (a b : ℤ) (x : ℤ × ℤ) :
    push a (push b x) = push b (push a x) := by
  apply Prod.ext <;> simp only [push] <;> ring

private theorem append (a : ℤ) (h : ℕ) :
    block a (h+1) = push (a+h) (block a h) := by
  induction h generalizing a with
  | zero => simp [block, push]
  | succ h ih =>
    change push a (block (a+1) (h+1)) = push (a+((h+1:ℕ):ℤ)) (push a (block (a+1) h))
    rw [ih, commute]
    push_cast
    rw [show a+1+h = a+(h+1) by ring]

/-- Pair the endpoints. Their indices always add to 2a+h-1. -/
private theorem reflection (h : ℕ) (a : ℤ) :
    ∃ u v : ℤ, (block a h).1 = 1+3*u ∧
      2*(block a h).2 = (2*a+h-1)*(h+3*v) := by
  induction h using Nat.strong_induction_on generalizing a with
  | h h ih =>
    cases h with
    | zero => exact ⟨0,0,by simp [block],by simp [block]⟩
    | succ h =>
      cases h with
      | zero => exact ⟨0,0,by simp [block,push],by simp [block,push]⟩
      | succ h =>
        obtain ⟨u,v,ha,hb⟩ := ih h (by omega) (a+1)
        let b : ℤ := a+1+h
        let x := block (a+1) h
        change x.1 = 1+3*u at ha
        change 2*x.2 = (2*(a+1)+h-1)*(h+3*v) at hb
        have form : block a (h+2) = push a (push b x) := by
          change push a (block (a+1) (h+1)) = _
          rw [append]
        rw [form]
        refine ⟨u-a*b*x.1-(a+b)*x.2, v-a*b*(h+3*v)+2*u, ?_, ?_⟩
        · simp only [push]
          linear_combination ha
        · have hb' : 2*x.2 = (a+b)*(h+3*v) := by
            dsimp [b]
            rw [hb]
            ring
          calc
            2*(push a (push b x)).2 = (1-3*a*b)*(2*x.2)+2*(a+b)*x.1 := by
              simp only [push]; ring
            _ = _ := by rw [hb',ha]; push_cast; dsimp [b]; ring

private theorem cancelUnit (e : ℕ) (u x : ℤ) (hu : IsCoprime (3:ℤ) u) :
    (3:ℤ)^e ∣ u*x ↔ (3:ℤ)^e ∣ x :=
  ⟨hu.pow_left.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h u⟩

/-- For every power of three, its divisibility at both indices agrees
    exactly with its divisibility in 3m. This determines both valuations. -/
theorem paired_powers (m e : ℕ) (hm : 0 < m) :
    ((3:ℤ)^e ∣ term (3*m-1) ↔ (3:ℤ)^e ∣ 3*(m:ℤ)) ∧
    ((3:ℤ)^e ∣ term (3*m) ↔ (3:ℤ)^e ∣ 3*(m:ℤ)) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  let j := 3*r+2
  have hj : 3*(r+1)-1 = j := by dsimp [j]; omega
  have hj' : 3*(r+1) = j+1 := by dsimp [j]; omega
  have idx : (j:ℤ) = 3*(r:ℤ)+2 := by dsimp [j]; push_cast; ring
  obtain ⟨u,v,ha,hb⟩ := reflection j 1
  let M : ℤ := 3*((r:ℤ)+1)
  have pre : 2*term j = (3*((r:ℤ)+v+1)-1)*M := by
    change 2*(block 1 j).2 = _
    rw [hb,idx]; dsimp [M]; ring
  have post : 2*term (j+1) = (3*((r:ℤ)+v+1+2*u)+1)*M := by
    change 2*(block 1 (j+1)).2 = _
    rw [append]
    simp only [push]
    change 2*term j = _ at pre
    change 2*(block 1 j).2 = _ at pre
    rw [mul_add,pre,ha,idx]; dsimp [M]; ring
  have two : IsCoprime (3:ℤ) 2 := ⟨1,-1,by decide⟩
  have minus (z : ℤ) : IsCoprime (3:ℤ) (3*z-1) := ⟨z,-1,by ring⟩
  have plus (z : ℤ) : IsCoprime (3:ℤ) (3*z+1) := ⟨-z,1,by ring⟩
  rw [hj,hj']
  push_cast
  constructor
  · exact (cancelUnit e 2 _ two).symm.trans (pre ▸ cancelUnit e _ M (minus _))
  · exact (cancelUnit e 2 _ two).symm.trans (post ▸ cancelUnit e _ M (plus _))
end A363412

#print axioms A363412.paired_powers
