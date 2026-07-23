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
module

public import FormalConjectures.Util.ProblemImports

@[expose] public section

/-!
# Kagey Problem 137

Starting at $0 \in \mathbb{Q}$, consider the operations
$f(x) = x + 1$ and $g(x) = -1/x$, with $g$ not applied at zero. This file
records the canonical shortest-path tree, the rank recurrence, and the
characterization of the blue vertices whose parent edge is an inversion edge.

*References:*
- [Peter Kagey, Problem 137](https://peterkagey.com/problems/137/)
- [OEIS A226247](https://oeis.org/A226247)
- [OEIS A097333](https://oeis.org/A097333)
-/

namespace OeisA226247

/-- The four non-root regions in the canonical shortest-path tree. -/
inductive State
  | root
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Canonical vertices, indexed by their rational region. -/
inductive Vertex : State → Type
  | root : Vertex .root
  | root_f : Vertex .B
  | a_f : Vertex .A → Vertex .A
  | b_f : Vertex .B → Vertex .A
  | c_f : Vertex .C → Vertex .B
  | a_g : Vertex .A → Vertex .C
  | b_g : Vertex .B → Vertex .D

/-- The rational value represented by a canonical vertex. -/
def value : {s : State} → Vertex s → ℚ
  | _, .root => 0
  | _, .root_f => 1
  | _, .a_f v => value v + 1
  | _, .b_f v => value v + 1
  | _, .c_f v => value v + 1
  | _, .a_g v => -1 / value v
  | _, .b_g v => -1 / value v

/-- Canonical depth. -/
def depth : {s : State} → Vertex s → ℕ
  | _, .root => 0
  | _, .root_f => 1
  | _, .a_f v => depth v + 1
  | _, .b_f v => depth v + 1
  | _, .c_f v => depth v + 1
  | _, .a_g v => depth v + 1
  | _, .b_g v => depth v + 1

/-- A canonical vertex with its state hidden. -/
abbrev AnyVertex := Σ s, Vertex s

/-- Rational evaluation of a state-hidden vertex. -/
def anyValue (v : AnyVertex) : ℚ := value v.2

/-- Depth of a state-hidden vertex. -/
def anyDepth (v : AnyVertex) : ℕ := depth v.2

/-- The two allowed operations. -/
inductive Op
  | f
  | g
  deriving DecidableEq, Repr

/-- The operation used by the canonical parent edge. -/
def incoming : {s : State} → Vertex s → Option Op
  | _, .root => none
  | _, .root_f => some .f
  | _, .a_f _ => some .f
  | _, .b_f _ => some .f
  | _, .c_f _ => some .f
  | _, .a_g _ => some .g
  | _, .b_g _ => some .g

/-- A vertex is blue when its canonical incoming edge is an inversion edge. -/
def IsBlue {s : State} (v : Vertex s) : Prop := incoming v = some .g

/-- A canonical vertex is blue exactly when its rational value is negative. -/
@[category research open, AMS 5 11]
theorem blue_iff_negative {s : State} (v : Vertex s) : IsBlue v ↔ value v < 0 := by
  sorry

/-- Translation. -/
def f (x : ℚ) : ℚ := x + 1

/-- Negative reciprocal, used only away from zero. -/
def g (x : ℚ) : ℚ := -1 / x

/-- Normalize one translation step back into the canonical tree. -/
def applyF : AnyVertex → AnyVertex
  | ⟨.root, .root⟩ => ⟨.B, .root_f⟩
  | ⟨.A, v⟩ => ⟨.A, .a_f v⟩
  | ⟨.B, v⟩ => ⟨.A, .b_f v⟩
  | ⟨.C, v⟩ => ⟨.B, .c_f v⟩
  | ⟨.D, .b_g .root_f⟩ => ⟨.root, .root⟩
  | ⟨.D, .b_g (.c_f (.a_g (.a_f v)))⟩ => ⟨.C, .a_g v⟩
  | ⟨.D, .b_g (.c_f (.a_g (.b_f v)))⟩ => ⟨.D, .b_g v⟩

/-- Normalize one nonzero inversion step back into the canonical tree. -/
def applyG : AnyVertex → Option AnyVertex
  | ⟨.root, .root⟩ => none
  | ⟨.A, v⟩ => some ⟨.C, .a_g v⟩
  | ⟨.B, v⟩ => some ⟨.D, .b_g v⟩
  | ⟨.C, .a_g v⟩ => some ⟨.A, v⟩
  | ⟨.D, .b_g v⟩ => some ⟨.B, v⟩

/-- Reachability in exactly $n$ valid operations, normalized after each step. -/
inductive Reach : ℕ → AnyVertex → Prop
  | root : Reach 0 ⟨.root, .root⟩
  | step_f {n : ℕ} {v : AnyVertex} : Reach n v → Reach (n + 1) (applyF v)
  | step_g {n : ℕ} {v w : AnyVertex} :
      Reach n v → applyG v = some w → Reach (n + 1) w

/-- Canonical depth is the true shortest-path rank. -/
@[category research open, AMS 5 11]
theorem depth_is_shortest {s : State} (v : Vertex s) :
    Reach (depth v) ⟨s, v⟩ ∧ ∀ n, Reach n ⟨s, v⟩ → depth v ≤ n := by
  sorry

/-- The number of canonical vertices in each state at each rank. -/
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

/-- Number of distinct rational vertices in rank $n$ of the canonical tree. -/
def a (n : ℕ) : ℕ :=
  stateCount n .root + stateCount n .A + stateCount n .B +
    stateCount n .C + stateCount n .D

/-- For every $n \geq 4$, $a(n) = a(n - 1) + a(n - 3)$. -/
@[category research open, AMS 5 11]
theorem rank_recurrence (n : ℕ) (hn : 4 ≤ n) :
    a n = a (n - 1) + a (n - 3) := by
  sorry

end OeisA226247
