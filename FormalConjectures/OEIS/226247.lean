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
The canonical shortest-path tree has four non-root regions:

* `A`: values greater than `1`;
* `B`: values in `(0, 1]`;
* `C`: values in `(-1, 0)`;
* `D`: values at most `-1`.

This file formalizes that canonical tree, its evaluation in the rationals,
the normalization of both operations, minimality of canonical depth, the
rank-count recurrence, and the characterization of blue vertices.

*References:*
- [OEIS A226247](https://oeis.org/A226247)
- [OEIS A097333](https://oeis.org/A097333)
- [Kagey Problem 137](https://peterkagey.com/problems/137/)
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

/--
Canonical vertices, indexed by their rational region.

The constructors are exactly the shortest-path child transitions:
the root has one `f`-child in `B`; `A` has an `f`-child in `A` and a
`g`-child in `C`; `B` has an `f`-child in `A` and a `g`-child in `D`;
`C` has an `f`-child in `B`; and `D` has no children.
-/
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

/-- The interval associated to each state. -/
def InRegion : State → ℚ → Prop
  | .root, x => x = 0
  | .A, x => 1 < x
  | .B, x => 0 < x ∧ x ≤ 1
  | .C, x => -1 < x ∧ x < 0
  | .D, x => x ≤ -1

@[category API, AMS 11]
theorem value_mem_region {s : State} (v : Vertex s) : InRegion s (value v) := by
  induction v with
  | root =>
      simp [InRegion, value]
  | root_f =>
      norm_num [InRegion, value]
  | a_f v ih =>
      simp [InRegion] at ih ⊢
      simp [value]
      linarith
  | b_f v ih =>
      simp [InRegion] at ih ⊢
      simp [value]
      linarith
  | c_f v ih =>
      simp [InRegion] at ih ⊢
      simp [value]
      constructor <;> linarith
  | a_g v ih =>
      simp [InRegion] at ih ⊢
      have hv0 : 0 < value v := lt_trans (by norm_num) ih
      have hfrac : 1 / value v < 1 := (div_lt_one hv0).2 ih
      constructor
      · simp [value]
        linarith
      · exact div_neg_of_neg_of_pos (by norm_num) hv0
  | b_g v ih =>
      simp [InRegion] at ih ⊢
      have hrecip : 1 ≤ 1 / value v := (le_div_iff₀ ih.1).2 (by simpa using ih.2)
      simp [value]
      linarith

@[category API, AMS 11]
theorem value_injective_same {s : State} :
    Function.Injective (fun v : Vertex s => value v) := by
  intro v
  induction v with
  | root =>
      intro w h
      cases w
      rfl
  | root_f =>
      intro w h
      cases w with
      | root_f => rfl
      | c_f w =>
          have hw := value_mem_region w
          simp [InRegion] at hw
          simp [value] at h
          exfalso
          linarith
  | a_f v ih =>
      intro w h
      cases w with
      | a_f w =>
          have hvw : value v = value w := by
            simpa [value] using h
          exact congrArg Vertex.a_f (ih w hvw)
      | b_f w =>
          have hv := value_mem_region v
          have hw := value_mem_region w
          simp [InRegion] at hv hw
          simp [value] at h
          exfalso
          linarith
  | b_f v ih =>
      intro w h
      cases w with
      | a_f w =>
          have hv := value_mem_region v
          have hw := value_mem_region w
          simp [InRegion] at hv hw
          simp [value] at h
          exfalso
          linarith
      | b_f w =>
          have hvw : value v = value w := by
            simpa [value] using h
          exact congrArg Vertex.b_f (ih w hvw)
  | c_f v ih =>
      intro w h
      cases w with
      | root_f =>
          have hv := value_mem_region v
          simp [InRegion] at hv
          simp [value] at h
          exfalso
          linarith
      | c_f w =>
          have hvw : value v = value w := by
            simpa [value] using h
          exact congrArg Vertex.c_f (ih w hvw)
  | a_g v ih =>
      intro w h
      cases w with
      | a_g w =>
          have hinv : (value v)⁻¹ = (value w)⁻¹ := by
            simpa [value, div_eq_mul_inv] using h
          exact congrArg Vertex.a_g (ih w (inv_injective.mp hinv))
  | b_g v ih =>
      intro w h
      cases w with
      | b_g w =>
          have hinv : (value v)⁻¹ = (value w)⁻¹ := by
            simpa [value, div_eq_mul_inv] using h
          exact congrArg Vertex.b_g (ih w (inv_injective.mp hinv))

@[category API, AMS 11]
theorem state_eq_of_value_eq {s t : State} (v : Vertex s) (w : Vertex t)
    (h : value v = value w) : s = t := by
  have hv := value_mem_region v
  have hw := value_mem_region w
  cases s <;> cases t <;> simp [InRegion] at hv hw ⊢ <;> try rfl <;> linarith

/-- A canonical vertex with its state hidden. -/
abbrev AnyVertex := Σ s, Vertex s

/-- Rational evaluation of a state-hidden vertex. -/
def anyValue (v : AnyVertex) : ℚ := value v.2

/-- Depth of a state-hidden vertex. -/
def anyDepth (v : AnyVertex) : ℕ := depth v.2

@[category API, AMS 11]
theorem anyValue_injective : Function.Injective anyValue := by
  rintro ⟨s, v⟩ ⟨t, w⟩ h
  have hst : s = t := state_eq_of_value_eq v w h
  cases hst
  have hvw : v = w := value_injective_same h
  cases hvw
  rfl

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

/-- A vertex is blue when its canonical incoming edge is a `g`-edge. -/
def IsBlue {s : State} (v : Vertex s) : Prop := incoming v = some .g

/--
A nonzero canonical vertex is blue if and only if its rational value is negative.
The root is automatically excluded: its incoming edge is `none` and its value is zero.
-/
@[category research solved, AMS 05 11]
theorem blue_iff_negative {s : State} (v : Vertex s) : IsBlue v ↔ value v < 0 := by
  cases v with
  | root =>
      norm_num [IsBlue, incoming, value]
  | root_f =>
      norm_num [IsBlue, incoming, value]
  | a_f v =>
      have hv := value_mem_region v
      simp [InRegion] at hv
      simp [IsBlue, incoming, value]
      linarith
  | b_f v =>
      have hv := value_mem_region v
      simp [InRegion] at hv
      simp [IsBlue, incoming, value]
      linarith
  | c_f v =>
      have hv := value_mem_region v
      simp [InRegion] at hv
      simp [IsBlue, incoming, value]
      linarith
  | a_g v =>
      have hv := value_mem_region v
      simp [InRegion] at hv
      have hv0 : 0 < value v := lt_trans (by norm_num) hv
      simp [IsBlue, incoming, value]
      exact div_neg_of_neg_of_pos (by norm_num) hv0
  | b_g v =>
      have hv := value_mem_region v
      simp [InRegion] at hv
      simp [IsBlue, incoming, value]
      exact div_neg_of_neg_of_pos (by norm_num) hv.1

/-- Translation. -/
def f (x : ℚ) : ℚ := x + 1

/-- Negative reciprocal. This is used only away from zero. -/
def g (x : ℚ) : ℚ := -1 / x

/--
Normalize one translation step back into the canonical tree.
The final three cases encode the relation that shortens an `f`-step from region `D`.
-/
def applyF : AnyVertex → AnyVertex
  | ⟨.root, .root⟩ => ⟨.B, .root_f⟩
  | ⟨.A, v⟩ => ⟨.A, .a_f v⟩
  | ⟨.B, v⟩ => ⟨.A, .b_f v⟩
  | ⟨.C, v⟩ => ⟨.B, .c_f v⟩
  | ⟨.D, .b_g .root_f⟩ => ⟨.root, .root⟩
  | ⟨.D, .b_g (.c_f (.a_g (.a_f v)))⟩ => ⟨.C, .a_g v⟩
  | ⟨.D, .b_g (.c_f (.a_g (.b_f v)))⟩ => ⟨.D, .b_g v⟩

/-- Normalize one nonzero negative-reciprocal step back into the canonical tree. -/
def applyG : AnyVertex → Option AnyVertex
  | ⟨.root, .root⟩ => none
  | ⟨.A, v⟩ => some ⟨.C, .a_g v⟩
  | ⟨.B, v⟩ => some ⟨.D, .b_g v⟩
  | ⟨.C, .a_g v⟩ => some ⟨.A, v⟩
  | ⟨.D, .b_g v⟩ => some ⟨.B, v⟩

private lemma f_reduce (x : ℚ) (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    -1 / (-1 / (x + 1) + 1) + 1 = -1 / x := by
  field_simp
  ring

@[category API, AMS 11]
theorem anyValue_applyF (v : AnyVertex) : anyValue (applyF v) = f (anyValue v) := by
  rcases v with ⟨s, v⟩
  cases v with
  | root =>
      norm_num [applyF, anyValue, value, f]
  | root_f =>
      norm_num [applyF, anyValue, value, f]
  | a_f v =>
      simp [applyF, anyValue, value, f]
  | b_f v =>
      simp [applyF, anyValue, value, f]
  | c_f v =>
      simp [applyF, anyValue, value, f]
  | a_g v =>
      simp [applyF, anyValue, value, f]
  | b_g v =>
      cases v with
      | root_f =>
          norm_num [applyF, anyValue, value, f]
      | c_f v =>
          cases v with
          | a_g v =>
              cases v with
              | a_f v =>
                  have hv := value_mem_region v
                  simp [InRegion] at hv
                  have hv0 : value v ≠ 0 := ne_of_gt (lt_trans (by norm_num) hv)
                  have hv1 : value v + 1 ≠ 0 := by linarith
                  simpa [applyF, anyValue, value, f] using f_reduce (value v) hv0 hv1
              | b_f v =>
                  have hv := value_mem_region v
                  simp [InRegion] at hv
                  have hv0 : value v ≠ 0 := ne_of_gt hv.1
                  have hv1 : value v + 1 ≠ 0 := by linarith
                  simpa [applyF, anyValue, value, f] using f_reduce (value v) hv0 hv1

private lemma g_involutive (x : ℚ) (hx : x ≠ 0) : g (g x) = x := by
  simp [g, hx]

@[category API, AMS 11]
theorem anyValue_applyG {v w : AnyVertex} (h : applyG v = some w) :
    anyValue w = g (anyValue v) := by
  rcases v with ⟨s, v⟩
  cases v with
  | root =>
      simp [applyG] at h
  | root_f =>
      simp [applyG] at h
      cases h
      rfl
  | a_f v =>
      simp [applyG] at h
      cases h
      rfl
  | b_f v =>
      simp [applyG] at h
      cases h
      rfl
  | c_f v =>
      simp [applyG] at h
      cases h
      rfl
  | a_g v =>
      simp [applyG] at h
      cases h
      have hv := value_mem_region v
      simp [InRegion] at hv
      have hv0 : value v ≠ 0 := ne_of_gt (lt_trans (by norm_num) hv)
      simpa [anyValue, value] using g_involutive (value v) hv0
  | b_g v =>
      simp [applyG] at h
      cases h
      have hv := value_mem_region v
      simp [InRegion] at hv
      have hv0 : value v ≠ 0 := ne_of_gt hv.1
      simpa [anyValue, value] using g_involutive (value v) hv0

@[category API, AMS 11]
theorem depth_applyF_le (v : AnyVertex) : anyDepth (applyF v) ≤ anyDepth v + 1 := by
  rcases v with ⟨s, v⟩
  cases v with
  | root =>
      simp [applyF, anyDepth, depth]
  | root_f =>
      simp [applyF, anyDepth, depth]
  | a_f v =>
      simp [applyF, anyDepth, depth]
  | b_f v =>
      simp [applyF, anyDepth, depth]
  | c_f v =>
      simp [applyF, anyDepth, depth]
  | a_g v =>
      simp [applyF, anyDepth, depth]
  | b_g v =>
      cases v with
      | root_f =>
          simp [applyF, anyDepth, depth]
      | c_f v =>
          cases v with
          | a_g v =>
              cases v with
              | a_f v =>
                  simp [applyF, anyDepth, depth]
                  omega
              | b_f v =>
                  simp [applyF, anyDepth, depth]
                  omega

@[category API, AMS 11]
theorem depth_applyG_le {v w : AnyVertex} (h : applyG v = some w) :
    anyDepth w ≤ anyDepth v + 1 := by
  rcases v with ⟨s, v⟩
  cases v <;> simp [applyG] at h
  all_goals cases h <;> simp [anyDepth, depth] <;> omega

/-- Reachability in exactly `n` valid operations, normalized after each step. -/
inductive Reach : ℕ → AnyVertex → Prop
  | root : Reach 0 ⟨.root, .root⟩
  | step_f {n : ℕ} {v : AnyVertex} : Reach n v → Reach (n + 1) (applyF v)
  | step_g {n : ℕ} {v w : AnyVertex} :
      Reach n v → applyG v = some w → Reach (n + 1) w

@[category API, AMS 11]
theorem depth_le_of_reach {n : ℕ} {v : AnyVertex} (h : Reach n v) : anyDepth v ≤ n := by
  induction h with
  | root =>
      simp [anyDepth, depth]
  | step_f h ih =>
      have hs := depth_applyF_le _
      omega
  | step_g h hg ih =>
      have hs := depth_applyG_le hg
      omega

@[category API, AMS 11]
theorem canonical_reach {s : State} (v : Vertex s) : Reach (depth v) ⟨s, v⟩ := by
  induction v with
  | root =>
      exact Reach.root
  | root_f =>
      simpa [depth, applyF] using Reach.step_f Reach.root
  | a_f v ih =>
      simpa [depth, applyF] using Reach.step_f ih
  | b_f v ih =>
      simpa [depth, applyF] using Reach.step_f ih
  | c_f v ih =>
      simpa [depth, applyF] using Reach.step_f ih
  | a_g v ih =>
      simpa [depth, applyG] using Reach.step_g ih (by rfl)
  | b_g v ih =>
      simpa [depth, applyG] using Reach.step_g ih (by rfl)

/-- Canonical depth is the true shortest-path rank. -/
@[category research solved, AMS 05 11]
theorem depth_is_shortest {s : State} (v : Vertex s) :
    Reach (depth v) ⟨s, v⟩ ∧ ∀ n, Reach n ⟨s, v⟩ → depth v ≤ n := by
  exact ⟨canonical_reach v, fun _ h => depth_le_of_reach h⟩

/--
The number of canonical vertices in each state at each rank.
This is the transfer recurrence read directly from the constructors of `Vertex`.
-/
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

/-- Number of distinct rational vertices in rank `n` of the canonical tree. -/
def a (n : ℕ) : ℕ :=
  stateCount n .root + stateCount n .A + stateCount n .B +
    stateCount n .C + stateCount n .D

@[category test, AMS 05 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 05 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 05 11]
theorem a_2 : a 2 = 2 := by rfl

@[category test, AMS 05 11]
theorem a_3 : a 3 = 2 := by rfl

@[category test, AMS 05 11]
theorem a_4 : a 4 = 3 := by rfl

@[category test, AMS 05 11]
theorem a_5 : a 5 = 5 := by rfl

@[category test, AMS 05 11]
theorem a_6 : a 6 = 7 := by rfl

/--
Let `a n` be the number of rational vertices first appearing in rank `n`.
Then, for every `n ≥ 4`,
`a n = a (n - 1) + a (n - 3)`.

This answers Kagey Problem 137 affirmatively.
-/
@[category research solved, AMS 05 11]
theorem rank_recurrence (n : ℕ) (hn : 4 ≤ n) :
    a n = a (n - 1) + a (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := by omega
  simp [a, stateCount]
  omega

#print axioms blue_iff_negative
#print axioms depth_is_shortest
#print axioms rank_recurrence

end OeisA226247
