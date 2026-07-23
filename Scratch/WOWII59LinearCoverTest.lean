import Mathlib

namespace WOWII59LinearCoverTest

set_option maxHeartbeats 0

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

#print axioms cycle_cover_linear

end WOWII59LinearCoverTest
