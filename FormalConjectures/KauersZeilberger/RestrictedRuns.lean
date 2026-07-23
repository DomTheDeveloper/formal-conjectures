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
# Standard Young tableaux with restricted runs

Kauers and Zeilberger's Conjecture 2a predicts the asymptotic number of
standard Young tableaux of rectangular shape `(n, n, n)` in which every
maximal string of consecutive entries lying in one row has length at least two.

We use the standard ballot-word encoding: the letter at position `m` records
the row containing `m`. Thus the tableaux are represented by words on three
letters with content `(n, n, n)`, ballot prefix inequalities, and no singleton
constant run.

*References:*

- [M. Kauers and D. Zeilberger, *Counting Standard Young Tableaux With
  Restricted Runs*](https://arxiv.org/abs/2006.10205)
- [D. Zeilberger, problem and bounty page](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/cyt.html)
-/

open Filter
open scoped Topology

namespace KauersZeilbergerRestrictedRuns

/-- A three-letter word of length `3n`. -/
abbrev Word (n : ℕ) := Fin (3 * n) → Fin 3

/-- The list representation of a fixed-length word. -/
def Word.toList {n : ℕ} (w : Word n) : List (Fin 3) :=
  List.ofFn w

/-- Every prefix has at least as many `0`s as `1`s and at least as many `1`s
as `2`s. -/
def IsBallot (w : List (Fin 3)) : Prop :=
  ∀ k : Fin (w.length + 1),
    (w.take k.1).count (0 : Fin 3) ≥ (w.take k.1).count (1 : Fin 3) ∧
      (w.take k.1).count (1 : Fin 3) ≥ (w.take k.1).count (2 : Fin 3)

/-- Every position has an equal adjacent letter. Equivalently, every maximal
constant run has length at least two. -/
def HasNoSingletonRuns (w : List (Fin 3)) : Prop :=
  ∀ i : Fin w.length,
    (0 < i.1 ∧ w.get? (i.1 - 1) = w.get? i.1) ∨
      w.get? (i.1 + 1) = w.get? i.1

/-- The ballot words corresponding to the tableaux counted in Conjecture 2a. -/
def IsAdmissible (n : ℕ) (w : Word n) : Prop :=
  let letters := w.toList
  letters.count (0 : Fin 3) = n ∧
    letters.count (1 : Fin 3) = n ∧
    letters.count (2 : Fin 3) = n ∧
    IsBallot letters ∧
    HasNoSingletonRuns letters

/-- Number of restricted-run tableaux, represented by their ballot words. -/
noncomputable def G (n : ℕ) : ℕ :=
  (Finset.univ.filter (IsAdmissible n)).card

/--
**Kauers–Zeilberger Conjecture 2a.**

There is a positive constant `C₁` such that

`G(n) ∼ C₁ · 8ⁿ / n⁴`.

The limit formulation avoids division by `n⁴` at `n = 0` while expressing the
same asymptotic assertion.
-/
@[category research open, AMS 05]
theorem conjecture_2a :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      Tendsto
        (fun n : ℕ => ((G n : ℝ) * (n : ℝ) ^ 4) / (8 : ℝ) ^ n)
        atTop (𝓝 C₁) := by
  sorry

end KauersZeilbergerRestrictedRuns
