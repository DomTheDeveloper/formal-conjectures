import Mathlib

namespace WOWII59CycleBridgeTest

open Finset

set_option maxHeartbeats 0

private def Contains3 (s : Finset (Fin 18)) (a b c : Fin 18) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s

private def Contains4 (s : Finset (Fin 18)) (a b c d : Fin 18) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s

private def Contains6 (s : Finset (Fin 18)) (a b c d e f : Fin 18) : Prop :=
  a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧ e ∈ s ∧ f ∈ s

private def bit (s : Finset (Fin 18)) (v : Fin 18) : ℕ := if v ∈ s then 1 else 0

private theorem bit_le_one (s : Finset (Fin 18)) (v : Fin 18) : bit s v ≤ 1 := by
  simp [bit]

private theorem bit3_le_two {s : Finset (Fin 18)} {a b c : Fin 18}
    (h : ¬ Contains3 s a b c) : bit s a + bit s b + bit s c ≤ 2 := by
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;> by_cases hc : c ∈ s <;>
    simp [Contains3, bit, ha, hb, hc] at h ⊢

private theorem bit4_le_three {s : Finset (Fin 18)} {a b c d : Fin 18}
    (h : ¬ Contains4 s a b c d) : bit s a + bit s b + bit s c + bit s d ≤ 3 := by
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;> by_cases hc : c ∈ s <;>
    by_cases hd : d ∈ s <;> simp [Contains4, bit, ha, hb, hc, hd] at h ⊢

private theorem bit6_le_five {s : Finset (Fin 18)} {a b c d e f : Fin 18}
    (h : ¬ Contains6 s a b c d e f) :
    bit s a + bit s b + bit s c + bit s d + bit s e + bit s f ≤ 5 := by
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;> by_cases hc : c ∈ s <;>
    by_cases hd : d ∈ s <;> by_cases he : e ∈ s <;> by_cases hf : f ∈ s <;>
      simp [Contains6, bit, ha, hb, hc, hd, he, hf] at h ⊢

private theorem bit_sum_eq_card (s : Finset (Fin 18)) :
    bit s 0 + bit s 1 + bit s 2 + bit s 3 + bit s 4 + bit s 5 +
      bit s 6 + bit s 7 + bit s 8 + bit s 9 + bit s 10 + bit s 11 +
      bit s 12 + bit s 13 + bit s 14 + bit s 15 + bit s 16 + bit s 17 = s.card := by
  have h : (∑ v : Fin 18, bit s v) = s.card := by simp [bit]
  simpa [Fin.sum_univ_succ] using h

private theorem cycle_cover_linear
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : ℕ)
    (hx0 : x0 ≤ 1) (hx1 : x1 ≤ 1) (hx2 : x2 ≤ 1) (hx3 : x3 ≤ 1)
    (hx4 : x4 ≤ 1) (hx5 : x5 ≤ 1) (hx6 : x6 ≤ 1) (hx7 : x7 ≤ 1)
    (hx8 : x8 ≤ 1) (hx9 : x9 ≤ 1) (hx10 : x10 ≤ 1) (hx11 : x11 ≤ 1)
    (hx12 : x12 ≤ 1) (hx13 : x13 ≤ 1) (hx14 : x14 ≤ 1) (hx15 : x15 ≤ 1)
    (hx16 : x16 ≤ 1) (hx17 : x17 ≤ 1)
    (h1 : x4 + x7 + x10 ≤ 2)
    (h2 : x1 + x5 + x3 + x8 ≤ 3)
    (h3 : x0 + x9 + x10 ≤ 2)
    (h4 : x2 + x6 + x4 + x9 ≤ 3)
    (h5 : x2 + x6 + x10 ≤ 2)
    (h6 : x1 + x6 + x3 + x7 ≤ 3)
    (h7 : x0 + x5 + x2 + x9 ≤ 3)
    (h8 : x1 + x5 + x4 + x6 ≤ 3)
    (h9 : x3 + x7 + x4 + x9 ≤ 3)
    (h10 : x0 + x5 + x3 + x8 ≤ 3)
    (h11 : x1 + x8 + x10 ≤ 2)
    (h12 : x3 + x5 + x10 ≤ 2)
    (h13 : x0 + x8 + x3 + x9 ≤ 3)
    (h14 : x0 + x5 + x1 + x8 ≤ 3)
    (h15 : x3 + x6 + x4 + x7 ≤ 3)
    (h16 : x1 + x6 + x4 + x7 ≤ 3)
    (h17 : x1 + x5 + x4 + x7 ≤ 3)
    (h18 : x1 + x6 + x3 + x8 ≤ 3)
    (h19 : x1 + x5 + x2 + x6 ≤ 3)
    (h20 : x0 + x8 + x1 + x6 + x2 + x9 ≤ 5)
    (h21 : x2 + x6 + x3 + x9 ≤ 3)
    (h22 : x2 + x5 + x4 + x6 ≤ 3)
    (h23 : x1 + x7 + x3 + x8 ≤ 3)
    (h24 : x0 + x8 + x1 + x7 + x4 + x9 ≤ 5)
    (h25 : x0 + x5 + x4 + x9 ≤ 3) :
    x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 +
      x12 + x13 + x14 + x15 + x16 + x17 ≤ 13 := by
  omega

private theorem cycle_cover :
    ∀ s : Finset (Fin 18), 14 ≤ s.card →
      Contains3 s 4 7 10 ∨
      Contains4 s 1 5 3 8 ∨
      Contains3 s 0 9 10 ∨
      Contains4 s 2 6 4 9 ∨
      Contains3 s 2 6 10 ∨
      Contains4 s 1 6 3 7 ∨
      Contains4 s 0 5 2 9 ∨
      Contains4 s 1 5 4 6 ∨
      Contains4 s 3 7 4 9 ∨
      Contains4 s 0 5 3 8 ∨
      Contains3 s 1 8 10 ∨
      Contains3 s 3 5 10 ∨
      Contains4 s 0 8 3 9 ∨
      Contains4 s 0 5 1 8 ∨
      Contains4 s 3 6 4 7 ∨
      Contains4 s 1 6 4 7 ∨
      Contains4 s 1 5 4 7 ∨
      Contains4 s 1 6 3 8 ∨
      Contains4 s 1 5 2 6 ∨
      Contains6 s 0 8 1 6 2 9 ∨
      Contains4 s 2 6 3 9 ∨
      Contains4 s 2 5 4 6 ∨
      Contains4 s 1 7 3 8 ∨
      Contains6 s 0 8 1 7 4 9 ∨
      Contains4 s 0 5 4 9 := by
  intro s hcard
  by_contra h
  simp only [not_or] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
  have g1 := bit3_le_two h1
  have g2 := bit4_le_three h2
  have g3 := bit3_le_two h3
  have g4 := bit4_le_three h4
  have g5 := bit3_le_two h5
  have g6 := bit4_le_three h6
  have g7 := bit4_le_three h7
  have g8 := bit4_le_three h8
  have g9 := bit4_le_three h9
  have g10 := bit4_le_three h10
  have g11 := bit3_le_two h11
  have g12 := bit3_le_two h12
  have g13 := bit4_le_three h13
  have g14 := bit4_le_three h14
  have g15 := bit4_le_three h15
  have g16 := bit4_le_three h16
  have g17 := bit4_le_three h17
  have g18 := bit4_le_three h18
  have g19 := bit4_le_three h19
  have g20 := bit6_le_five h20
  have g21 := bit4_le_three h21
  have g22 := bit4_le_three h22
  have g23 := bit4_le_three h23
  have g24 := bit6_le_five h24
  have g25 := bit4_le_three h25
  have hx0 := bit_le_one s 0
  have hx1 := bit_le_one s 1
  have hx2 := bit_le_one s 2
  have hx3 := bit_le_one s 3
  have hx4 := bit_le_one s 4
  have hx5 := bit_le_one s 5
  have hx6 := bit_le_one s 6
  have hx7 := bit_le_one s 7
  have hx8 := bit_le_one s 8
  have hx9 := bit_le_one s 9
  have hx10 := bit_le_one s 10
  have hx11 := bit_le_one s 11
  have hx12 := bit_le_one s 12
  have hx13 := bit_le_one s 13
  have hx14 := bit_le_one s 14
  have hx15 := bit_le_one s 15
  have hx16 := bit_le_one s 16
  have hx17 := bit_le_one s 17
  have hsum := bit_sum_eq_card s
  have hbound := cycle_cover_linear
    (bit s 0) (bit s 1) (bit s 2) (bit s 3) (bit s 4) (bit s 5)
    (bit s 6) (bit s 7) (bit s 8) (bit s 9) (bit s 10) (bit s 11)
    (bit s 12) (bit s 13) (bit s 14) (bit s 15) (bit s 16) (bit s 17)
    hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17
    g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20
    g21 g22 g23 g24 g25
  omega

#print axioms cycle_cover

end WOWII59CycleBridgeTest
