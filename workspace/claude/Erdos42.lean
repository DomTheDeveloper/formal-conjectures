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

import FormalConjectures.ErdosProblems.«42»

/-!
# `erdos_42.variants.constructive` is not an additional open problem

`FormalConjectures/ErdosProblems/42.lean` contains two statements:

* `erdos_42`, tagged `research solved` with `answer(True)` and a linked
  external Lean 4 proof, whose right-hand side is
  `∀ M ≥ 1, ∀ᶠ N in atTop, Q M N`;
* `erdos_42.variants.constructive`, tagged `research open`, whose right-hand
  side is `∃ f : ℕ → ℕ, ∀ M N, 1 ≤ M → f M ≤ N → Q M N`, described as "a
  variant asking for explicit bounds".

But `∀ᶠ N in atTop, …` unfolds to `∃ a, ∀ N ≥ a, …`, so the second statement
is exactly the first with the bounds collected into a function by choice —
the two are equivalent in Lean (`Filter.eventually_atTop` plus `choose`).
The "constructive" variant is therefore the *same* problem as the one already
recorded as solved, not a further open question, and its answer is `True`.

Note this is a statement about the formalization only: the `∃ f` here is a
classical existence claim, and `choose` extracts no computational content, so
the formal statement does not express the informal request for an *explicit*
bound. Capturing that would require naming a concrete `f` (e.g.
`answer(fun M => …)` with a stated growth rate).
-/

open Function Set Filter
open scoped Pointwise

namespace Erdos42Resolution

/-- The right-hand side of `erdos_42.variants.constructive` is equivalent to
the right-hand side of `erdos_42` (which is tagged `research solved`). -/
theorem constructive_iff_eventually :
    (∃ (f : ℕ → ℕ), ∀ (M N : ℕ) (_ : 1 ≤ M) (_ : f M ≤ N),
      ∀ (A : Set ℕ) (_ : IsMaximalSidonSetIn A N), ∃ᵉ (B : Set ℕ),
        B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
        ((A - A) ∩ (B - B)) = {0})
    ↔
    (∀ M ≥ 1, ∀ᶠ N in atTop, ∀ (A : Set ℕ) (_ : IsMaximalSidonSetIn A N),
      ∃ᵉ (B : Set ℕ), B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
        ((A - A) ∩ (B - B)) = {0}) := by
  constructor
  · rintro ⟨f, hf⟩ M hM
    exact Filter.eventually_atTop.mpr ⟨f M, fun N hN => hf M N hM hN⟩
  · intro h
    have hchoice : ∀ M : ℕ, ∃ a : ℕ, ∀ N : ℕ, a ≤ N → 1 ≤ M →
        ∀ (A : Set ℕ) (_ : IsMaximalSidonSetIn A N), ∃ᵉ (B : Set ℕ),
          B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
          ((A - A) ∩ (B - B)) = {0} := by
      intro M
      by_cases hM : 1 ≤ M
      · obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp (h M hM)
        exact ⟨a, fun N hN _ => ha N hN⟩
      · exact ⟨0, fun N _ hM' => absurd hM' hM⟩
    choose f hf using hchoice
    exact ⟨f, fun M N hM hfN => hf M N hfN hM⟩

end Erdos42Resolution
