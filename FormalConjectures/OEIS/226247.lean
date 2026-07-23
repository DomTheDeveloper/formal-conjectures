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

import FormalConjectures.Util.ProblemImports

/-!
# OEIS A226247 and Kagey Problem 137

Starting at `0 : ℚ`, consider the two operations
`f x = x + 1` and `g x = -1 / x` (with `g` not applied at zero).

*References:*
- [OEIS A226247](https://oeis.org/A226247)
- [OEIS A097333](https://oeis.org/A097333)
- [Kagey Problem 137](https://peterkagey.com/problems/137/)
-/

namespace OeisA226247

inductive State
  | root | A | B | C | D
  deriving DecidableEq, Repr

inductive Vertex : State → Type
  | root : Vertex .root
  | root_f : Vertex .B
  | a_f : Vertex .A → Vertex .A
  | b_f : Vertex .B → Vertex .A
  | c_f : Vertex .C → Vertex .B
  | a_g : Vertex .A → Vertex .C
  | b_g : Vertex .B → Vertex .D

def value : {s : State} → Vertex s → ℚ
  | _, .root => 0
  | _, .root_f => 1
  | _, .a_f v => value v + 1
  | _, .b_f v => value v + 1
  | _, .c_f v => value v + 1
  | _, .a_g v => -1 / value v
  | _, .b_g v => -1 / value v

inductive Op | f | g deriving DecidableEq, Repr

def incoming : {s : State} → Vertex s → Option Op
  | _, .root => none
  | _, .root_f => some .f
  | _, .a_f _ => some .f
  | _, .b_f _ => some .f
  | _, .c_f _ => some .f
  | _, .a_g _ => some .g
  | _, .b_g _ => some .g

def IsBlue {s : State} (v : Vertex s) : Prop := incoming v = some .g

@[category research open, AMS 05 11]
theorem blue_iff_negative {s : State} (v : Vertex s) : IsBlue v ↔ value v < 0 := by
  sorry

def stateCount : ℕ → State → ℕ
  | 0, .root => 1
  | 0, .A => 0
  | 0, .B => 0
  | 0, .C => 0
  | 0, .D => 0
  | n + 1, .root => 0
  | n + 1, .A => stateCount n .A + stateCount n .B
  | n + 1, .B => stateCount n .root + stateCount n .C
  | n + 1, .C => stateCount n .A
  | n + 1, .D => stateCount n .B

def a (n : ℕ) : ℕ :=
  stateCount n .root + stateCount n .A + stateCount n .B +
    stateCount n .C + stateCount n .D

@[category research open, AMS 05 11]
theorem rank_recurrence (n : ℕ) (hn : 4 ≤ n) :
    a n = a (n - 1) + a (n - 3) := by
  sorry

end OeisA226247
