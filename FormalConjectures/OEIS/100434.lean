/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# OEIS A100434: a false auxiliary-sequence conjecture

A100434 is the integer sequence with generating function

$$(1+x)(3+x)/(1+6x^2+x^4),$$

beginning `3, 4, -17, -24, 99, 140, ...`.

The entry also records auxiliary integer sequences and conjectures that

`c n + d n = e n + f n = g n + h n`

and

`c n + d n = b n`

for every natural number `n`. Here `h` is the auxiliary sequence called `a`
in the first sentence of the OEIS comment and `h` in its concluding sentence;
the name `a` is reserved for the primary OEIS sequence as required by this
repository's conventions.

The second claimed equality is already false at `n = 2`: the definitions give
`c 2 = -7`, `d 2 = -10`, and `b 2 = c 3 = 17`, so it would imply
`-17 = 17`.

*References:*
- [OEIS A100434](https://oeis.org/A100434)
-/

namespace OeisA100434

/-- A100434, defined by the order-four recurrence from its generating function. -/
def a : ℕ → ℤ
  | 0 => 3
  | 1 => 4
  | 2 => -17
  | 3 => -24
  | n + 4 => -6 * a (n + 2) - a n

@[category test, AMS 11]
theorem a_0 : a 0 = 3 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_2 : a 2 = -17 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_3 : a 3 = -24 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_4 : a 4 = 99 := by
  norm_num [a]

@[category test, AMS 11]
theorem a_5 : a 5 = 140 := by
  norm_num [a]

/-- The positive Pell companion values `1, 3, 7, 17, 41, ...`. -/
def cAbs : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | n + 2 => 2 * cAbs (n + 1) + cAbs n

/-- The auxiliary sequence `c` from the OEIS comment. -/
def c (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ ((n + 1) / 2) * cAbs n

/-- The positive values `2, 4, 10, 24, 58, ...`. -/
def dAbs : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | n + 2 => 2 * dAbs (n + 1) + dAbs n

/-- The auxiliary sequence `d` from the OEIS comment. -/
def d (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ (n / 2) * dAbs n

/-- The sequence obtained by swapping consecutive terms of `c`. -/
def b (n : ℕ) : ℤ :=
  if n % 2 = 0 then c (n + 1) else c (n - 1)

/-- The auxiliary sequence `e` from the OEIS comment. -/
def e (n : ℕ) : ℤ :=
  if n % 2 = 0 then d n / 2 else -(d (n - 1) / 2)

/-- The auxiliary sequence `f` from the OEIS comment. -/
def f (n : ℕ) : ℤ :=
  if n % 2 = 0 then d (n + 1) / 2 else d n / 2

/-- The auxiliary sequence `g` from the OEIS comment. -/
def g (n : ℕ) : ℤ :=
  if n % 2 = 0 then 0 else c n

/-- The auxiliary sequence called `a` and later `h` in the OEIS comment. -/
def h (n : ℕ) : ℤ :=
  if n % 2 = 0 then -c (n + 1) else d n

/--
"Then a(2n) = - c(2n+1), a(2n+1) = d(2n+1) and we have the following
conjectures: c(n) + d(n) = e(n) + f(n) = g(n) + a(n); c(n) + d(n) = b(n)."

This auxiliary-sequence conjecture recorded in OEIS A100434 is false. The
last equality fails at `n = 2`.
-/
@[category research solved, AMS 11]
theorem a100434_conjecture_false :
    ¬ ∀ n : ℕ,
      c n + d n = e n + f n ∧
      e n + f n = g n + h n ∧
      c n + d n = b n := by
  intro conjecture
  have h2 := (conjecture 2).2.2
  norm_num [b, c, d, cAbs, dAbs] at h2

end OeisA100434
