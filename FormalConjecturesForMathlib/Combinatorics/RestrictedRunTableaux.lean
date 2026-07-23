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

public import Mathlib

@[expose] public section

/-!
# Ballot words for standard Young tableaux with restricted runs

This file supplies the finite definitions used to state Kauers and
Zeilberger's restricted-run tableau conjectures.
-/

namespace RestrictedRunTableaux

/-- A three-letter word of length `3 * n`. -/
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

/-- A ballot word of content `(n, n, n)` with no singleton constant run. -/
def IsAdmissible (n : ℕ) (w : Word n) : Prop :=
  let letters := w.toList
  letters.count (0 : Fin 3) = n ∧
    letters.count (1 : Fin 3) = n ∧
    letters.count (2 : Fin 3) = n ∧
    IsBallot letters ∧
    HasNoSingletonRuns letters

/-- Number of restricted-run tableaux, represented by their ballot words. -/
def G (n : ℕ) : ℕ :=
  (Finset.univ.filter (IsAdmissible n)).card

end RestrictedRunTableaux
