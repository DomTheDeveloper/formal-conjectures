module

public import A038098.Sieve
public import Mathlib.Data.Rat.Cast.Order

/-! Unconditional instances of Sun's inequality. The numerals below are witnesses.
Each prime count is proved from the preceding count by the kernel-checked bit sieve. -/

public section
namespace Sun.CubeSieve

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem pi_255 : Nat.primeCounting 255 = 54 := by decide +kernel

private theorem pi_65791 : Nat.primeCounting 65791 = 6572 :=
  primeCounting_extend (width := 65536) (b := 256) (d := 13) pi_255
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_131327 : Nat.primeCounting 131327 = 12271 :=
  primeCounting_extend (width := 65536) (b := 362) (d := 13) pi_65791
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_196863 : Nat.primeCounting 196863 = 17724 :=
  primeCounting_extend (width := 65536) (b := 443) (d := 13) pi_131327
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_262399 : Nat.primeCounting 262399 = 23022 :=
  primeCounting_extend (width := 65536) (b := 512) (d := 13) pi_196863
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_327935 : Nat.primeCounting 327935 = 28245 :=
  primeCounting_extend (width := 65536) (b := 572) (d := 13) pi_262399
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_393471 : Nat.primeCounting 393471 = 33352 :=
  primeCounting_extend (width := 65536) (b := 627) (d := 13) pi_327935
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_459007 : Nat.primeCounting 459007 = 38391 :=
  primeCounting_extend (width := 65536) (b := 677) (d := 13) pi_393471
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_524543 : Nat.primeCounting 524543 = 43407 :=
  primeCounting_extend (width := 65536) (b := 724) (d := 13) pi_459007
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_590079 : Nat.primeCounting 590079 = 48357 :=
  primeCounting_extend (width := 65536) (b := 768) (d := 13) pi_524543
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_655615 : Nat.primeCounting 655615 = 53248 :=
  primeCounting_extend (width := 65536) (b := 809) (d := 13) pi_590079
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_721151 : Nat.primeCounting 721151 = 58121 :=
  primeCounting_extend (width := 65536) (b := 849) (d := 13) pi_655615
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_786687 : Nat.primeCounting 786687 = 62960 :=
  primeCounting_extend (width := 65536) (b := 886) (d := 13) pi_721151
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_852223 : Nat.primeCounting 852223 = 67781 :=
  primeCounting_extend (width := 65536) (b := 923) (d := 13) pi_786687
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_917759 : Nat.primeCounting 917759 = 72568 :=
  primeCounting_extend (width := 65536) (b := 957) (d := 13) pi_852223
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_983295 : Nat.primeCounting 983295 = 77299 :=
  primeCounting_extend (width := 65536) (b := 991) (d := 13) pi_917759
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1048831 : Nat.primeCounting 1048831 = 82044 :=
  primeCounting_extend (width := 65536) (b := 1024) (d := 13) pi_983295
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1114367 : Nat.primeCounting 1114367 = 86772 :=
  primeCounting_extend (width := 65536) (b := 1055) (d := 13) pi_1048831
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1179903 : Nat.primeCounting 1179903 = 91481 :=
  primeCounting_extend (width := 65536) (b := 1086) (d := 13) pi_1114367
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1245439 : Nat.primeCounting 1245439 = 96124 :=
  primeCounting_extend (width := 65536) (b := 1115) (d := 13) pi_1179903
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1310975 : Nat.primeCounting 1310975 = 100801 :=
  primeCounting_extend (width := 65536) (b := 1144) (d := 13) pi_1245439
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1376511 : Nat.primeCounting 1376511 = 105428 :=
  primeCounting_extend (width := 65536) (b := 1173) (d := 13) pi_1310975
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1442047 : Nat.primeCounting 1442047 = 110071 :=
  primeCounting_extend (width := 65536) (b := 1200) (d := 13) pi_1376511
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1507583 : Nat.primeCounting 1507583 = 114714 :=
  primeCounting_extend (width := 65536) (b := 1227) (d := 13) pi_1442047
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1573119 : Nat.primeCounting 1573119 = 119285 :=
  primeCounting_extend (width := 65536) (b := 1254) (d := 13) pi_1507583
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1638655 : Nat.primeCounting 1638655 = 123854 :=
  primeCounting_extend (width := 65536) (b := 1280) (d := 13) pi_1573119
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1704191 : Nat.primeCounting 1704191 = 128431 :=
  primeCounting_extend (width := 65536) (b := 1305) (d := 13) pi_1638655
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1769727 : Nat.primeCounting 1769727 = 132951 :=
  primeCounting_extend (width := 65536) (b := 1330) (d := 13) pi_1704191
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1835263 : Nat.primeCounting 1835263 = 137539 :=
  primeCounting_extend (width := 65536) (b := 1354) (d := 13) pi_1769727
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1900799 : Nat.primeCounting 1900799 = 142088 :=
  primeCounting_extend (width := 65536) (b := 1378) (d := 13) pi_1835263
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_1966335 : Nat.primeCounting 1966335 = 146617 :=
  primeCounting_extend (width := 65536) (b := 1402) (d := 13) pi_1900799
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2031871 : Nat.primeCounting 2031871 = 151140 :=
  primeCounting_extend (width := 65536) (b := 1425) (d := 13) pi_1966335
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2097407 : Nat.primeCounting 2097407 = 155626 :=
  primeCounting_extend (width := 65536) (b := 1448) (d := 13) pi_2031871
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2162943 : Nat.primeCounting 2162943 = 160157 :=
  primeCounting_extend (width := 65536) (b := 1470) (d := 13) pi_2097407
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2228479 : Nat.primeCounting 2228479 = 164614 :=
  primeCounting_extend (width := 65536) (b := 1492) (d := 13) pi_2162943
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2294015 : Nat.primeCounting 2294015 = 169106 :=
  primeCounting_extend (width := 65536) (b := 1514) (d := 13) pi_2228479
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2359551 : Nat.primeCounting 2359551 = 173534 :=
  primeCounting_extend (width := 65536) (b := 1536) (d := 13) pi_2294015
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2425087 : Nat.primeCounting 2425087 = 177995 :=
  primeCounting_extend (width := 65536) (b := 1557) (d := 13) pi_2359551
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2490623 : Nat.primeCounting 2490623 = 182440 :=
  primeCounting_extend (width := 65536) (b := 1578) (d := 13) pi_2425087
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2556159 : Nat.primeCounting 2556159 = 186885 :=
  primeCounting_extend (width := 65536) (b := 1598) (d := 13) pi_2490623
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2621695 : Nat.primeCounting 2621695 = 191323 :=
  primeCounting_extend (width := 65536) (b := 1619) (d := 13) pi_2556159
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2687231 : Nat.primeCounting 2687231 = 195768 :=
  primeCounting_extend (width := 65536) (b := 1639) (d := 13) pi_2621695
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2752767 : Nat.primeCounting 2752767 = 200186 :=
  primeCounting_extend (width := 65536) (b := 1659) (d := 13) pi_2687231
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2803221 : Nat.primeCounting 2803221 = 203581 :=
  primeCounting_extend (width := 50454) (b := 1674) (d := 13) pi_2752767
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2863288 : Nat.primeCounting 2863288 = 207663 :=
  primeCounting_extend (width := 60067) (b := 1692) (d := 13) pi_2803221
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2924207 : Nat.primeCounting 2924207 = 211737 :=
  primeCounting_extend (width := 60919) (b := 1710) (d := 13) pi_2863288
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_2985984 : Nat.primeCounting 2985984 = 215880 :=
  primeCounting_extend (width := 61777) (b := 1728) (d := 13) pi_2924207
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3048625 : Nat.primeCounting 3048625 = 220046 :=
  primeCounting_extend (width := 62641) (b := 1746) (d := 13) pi_2985984
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3112136 : Nat.primeCounting 3112136 = 224307 :=
  primeCounting_extend (width := 63511) (b := 1764) (d := 13) pi_3048625
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3176523 : Nat.primeCounting 3176523 = 228623 :=
  primeCounting_extend (width := 64387) (b := 1782) (d := 13) pi_3112136
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3241792 : Nat.primeCounting 3241792 = 233036 :=
  primeCounting_extend (width := 65269) (b := 1800) (d := 13) pi_3176523
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3307328 : Nat.primeCounting 3307328 = 237387 :=
  primeCounting_extend (width := 65536) (b := 1818) (d := 13) pi_3241792
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3307949 : Nat.primeCounting 3307949 = 237427 :=
  primeCounting_extend (width := 621) (b := 1818) (d := 7) pi_3307328
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3373485 : Nat.primeCounting 3373485 = 241768 :=
  primeCounting_extend (width := 65536) (b := 1836) (d := 13) pi_3307949
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3375000 : Nat.primeCounting 3375000 = 241867 :=
  primeCounting_extend (width := 1515) (b := 1837) (d := 8) pi_3373485
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3440536 : Nat.primeCounting 3440536 = 246272 :=
  primeCounting_extend (width := 65536) (b := 1854) (d := 13) pi_3375000
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3442951 : Nat.primeCounting 3442951 = 246434 :=
  primeCounting_extend (width := 2415) (b := 1855) (d := 9) pi_3440536
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3508487 : Nat.primeCounting 3508487 = 250700 :=
  primeCounting_extend (width := 65536) (b := 1873) (d := 13) pi_3442951
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3511808 : Nat.primeCounting 3511808 = 250923 :=
  primeCounting_extend (width := 3321) (b := 1873) (d := 9) pi_3508487
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3577344 : Nat.primeCounting 3577344 = 255226 :=
  primeCounting_extend (width := 65536) (b := 1891) (d := 13) pi_3511808
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3581577 : Nat.primeCounting 3581577 = 255492 :=
  primeCounting_extend (width := 4233) (b := 1892) (d := 10) pi_3577344
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3647113 : Nat.primeCounting 3647113 = 259890 :=
  primeCounting_extend (width := 65536) (b := 1909) (d := 13) pi_3581577
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3652264 : Nat.primeCounting 3652264 = 260196 :=
  primeCounting_extend (width := 5151) (b := 1911) (d := 10) pi_3647113
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3717800 : Nat.primeCounting 3717800 = 264568 :=
  primeCounting_extend (width := 65536) (b := 1928) (d := 13) pi_3652264
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3723875 : Nat.primeCounting 3723875 = 264974 :=
  primeCounting_extend (width := 6075) (b := 1929) (d := 10) pi_3717800
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3789411 : Nat.primeCounting 3789411 = 269292 :=
  primeCounting_extend (width := 65536) (b := 1946) (d := 13) pi_3723875
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3796416 : Nat.primeCounting 3796416 = 269738 :=
  primeCounting_extend (width := 7005) (b := 1948) (d := 10) pi_3789411
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3861952 : Nat.primeCounting 3861952 = 274097 :=
  primeCounting_extend (width := 65536) (b := 1965) (d := 13) pi_3796416
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3869893 : Nat.primeCounting 3869893 = 274614 :=
  primeCounting_extend (width := 7941) (b := 1967) (d := 10) pi_3861952
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3935429 : Nat.primeCounting 3935429 = 278941 :=
  primeCounting_extend (width := 65536) (b := 1983) (d := 13) pi_3869893
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_3944312 : Nat.primeCounting 3944312 = 279536 :=
  primeCounting_extend (width := 8883) (b := 1986) (d := 11) pi_3935429
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_4009848 : Nat.primeCounting 4009848 = 283796 :=
  primeCounting_extend (width := 65536) (b := 2002) (d := 13) pi_3944312
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_4019679 : Nat.primeCounting 4019679 = 284446 :=
  primeCounting_extend (width := 9831) (b := 2004) (d := 11) pi_4009848
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_4085215 : Nat.primeCounting 4085215 = 288783 :=
  primeCounting_extend (width := 65536) (b := 2021) (d := 13) pi_4019679
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_4096000 : Nat.primeCounting 4096000 = 289511 :=
  primeCounting_extend (width := 10785) (b := 2023) (d := 11) pi_4085215
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_4161536 : Nat.primeCounting 4161536 = 293777 :=
  primeCounting_extend (width := 65536) (b := 2039) (d := 13) pi_4096000
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

private theorem pi_4173281 : Nat.primeCounting 4173281 = 294552 :=
  primeCounting_extend (width := 11745) (b := 2042) (d := 11) pi_4161536
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)

def Cube (n : ℕ) : Prop := (((n+1)^3).primeCounting : ℚ) / (((n+1 : ℕ)^3 : ℕ) : ℚ) <
  ((n^3).primeCounting : ℚ) / ((n^3 : ℕ) : ℚ)

private theorem cube_141 : Cube 141 := by
  change (Nat.primeCounting 2863288 : ℚ) / 2863288 < (Nat.primeCounting 2803221 : ℚ) / 2803221
  rw [pi_2803221,pi_2863288]
  decide +kernel

private theorem cube_142 : Cube 142 := by
  change (Nat.primeCounting 2924207 : ℚ) / 2924207 < (Nat.primeCounting 2863288 : ℚ) / 2863288
  rw [pi_2863288,pi_2924207]
  decide +kernel

private theorem cube_143 : Cube 143 := by
  change (Nat.primeCounting 2985984 : ℚ) / 2985984 < (Nat.primeCounting 2924207 : ℚ) / 2924207
  rw [pi_2924207,pi_2985984]
  decide +kernel

private theorem cube_144 : Cube 144 := by
  change (Nat.primeCounting 3048625 : ℚ) / 3048625 < (Nat.primeCounting 2985984 : ℚ) / 2985984
  rw [pi_2985984,pi_3048625]
  decide +kernel

private theorem cube_145 : Cube 145 := by
  change (Nat.primeCounting 3112136 : ℚ) / 3112136 < (Nat.primeCounting 3048625 : ℚ) / 3048625
  rw [pi_3048625,pi_3112136]
  decide +kernel

private theorem cube_146 : Cube 146 := by
  change (Nat.primeCounting 3176523 : ℚ) / 3176523 < (Nat.primeCounting 3112136 : ℚ) / 3112136
  rw [pi_3112136,pi_3176523]
  decide +kernel

private theorem cube_147 : Cube 147 := by
  change (Nat.primeCounting 3241792 : ℚ) / 3241792 < (Nat.primeCounting 3176523 : ℚ) / 3176523
  rw [pi_3176523,pi_3241792]
  decide +kernel

private theorem cube_148 : Cube 148 := by
  change (Nat.primeCounting 3307949 : ℚ) / 3307949 < (Nat.primeCounting 3241792 : ℚ) / 3241792
  rw [pi_3241792,pi_3307949]
  decide +kernel

private theorem cube_149 : Cube 149 := by
  change (Nat.primeCounting 3375000 : ℚ) / 3375000 < (Nat.primeCounting 3307949 : ℚ) / 3307949
  rw [pi_3307949,pi_3375000]
  decide +kernel

private theorem cube_150 : Cube 150 := by
  change (Nat.primeCounting 3442951 : ℚ) / 3442951 < (Nat.primeCounting 3375000 : ℚ) / 3375000
  rw [pi_3375000,pi_3442951]
  decide +kernel

private theorem cube_151 : Cube 151 := by
  change (Nat.primeCounting 3511808 : ℚ) / 3511808 < (Nat.primeCounting 3442951 : ℚ) / 3442951
  rw [pi_3442951,pi_3511808]
  decide +kernel

private theorem cube_152 : Cube 152 := by
  change (Nat.primeCounting 3581577 : ℚ) / 3581577 < (Nat.primeCounting 3511808 : ℚ) / 3511808
  rw [pi_3511808,pi_3581577]
  decide +kernel

private theorem cube_153 : Cube 153 := by
  change (Nat.primeCounting 3652264 : ℚ) / 3652264 < (Nat.primeCounting 3581577 : ℚ) / 3581577
  rw [pi_3581577,pi_3652264]
  decide +kernel

private theorem cube_154 : Cube 154 := by
  change (Nat.primeCounting 3723875 : ℚ) / 3723875 < (Nat.primeCounting 3652264 : ℚ) / 3652264
  rw [pi_3652264,pi_3723875]
  decide +kernel

private theorem cube_155 : Cube 155 := by
  change (Nat.primeCounting 3796416 : ℚ) / 3796416 < (Nat.primeCounting 3723875 : ℚ) / 3723875
  rw [pi_3723875,pi_3796416]
  decide +kernel

private theorem cube_156 : Cube 156 := by
  change (Nat.primeCounting 3869893 : ℚ) / 3869893 < (Nat.primeCounting 3796416 : ℚ) / 3796416
  rw [pi_3796416,pi_3869893]
  decide +kernel

private theorem cube_157 : Cube 157 := by
  change (Nat.primeCounting 3944312 : ℚ) / 3944312 < (Nat.primeCounting 3869893 : ℚ) / 3869893
  rw [pi_3869893,pi_3944312]
  decide +kernel

private theorem cube_158 : Cube 158 := by
  change (Nat.primeCounting 4019679 : ℚ) / 4019679 < (Nat.primeCounting 3944312 : ℚ) / 3944312
  rw [pi_3944312,pi_4019679]
  decide +kernel

private theorem cube_159 : Cube 159 := by
  change (Nat.primeCounting 4096000 : ℚ) / 4096000 < (Nat.primeCounting 4019679 : ℚ) / 4019679
  rw [pi_4019679,pi_4096000]
  decide +kernel

private theorem cube_160 : Cube 160 := by
  change (Nat.primeCounting 4173281 : ℚ) / 4173281 < (Nat.primeCounting 4096000 : ℚ) / 4096000
  rw [pi_4096000,pi_4173281]
  decide +kernel

theorem cubes_141_to_160 (n : ℕ) (h₁ : 141 ≤ n) (h₂ : n ≤ 160) : Cube n := by
  have h : n = 141 ∨ n = 142 ∨ n = 143 ∨ n = 144 ∨ n = 145 ∨ n = 146 ∨ n = 147 ∨ n = 148 ∨ n = 149 ∨ n = 150 ∨ n = 151 ∨ n = 152 ∨ n = 153 ∨ n = 154 ∨ n = 155 ∨ n = 156 ∨ n = 157 ∨ n = 158 ∨ n = 159 ∨ n = 160 := by omega
  rcases h with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
  · exact cube_141
  · exact cube_142
  · exact cube_143
  · exact cube_144
  · exact cube_145
  · exact cube_146
  · exact cube_147
  · exact cube_148
  · exact cube_149
  · exact cube_150
  · exact cube_151
  · exact cube_152
  · exact cube_153
  · exact cube_154
  · exact cube_155
  · exact cube_156
  · exact cube_157
  · exact cube_158
  · exact cube_159
  · exact cube_160

end Sun.CubeSieve
#print axioms Sun.CubeSieve.cubes_141_to_160
