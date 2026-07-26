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

import FormalConjectures.Wikipedia.SteinerSystem

/-!
# Solutions to statements that are much easier than the mathematics they cite

## `SteinerSystems.infinitely_many_steiner_t4` / `infinitely_many_steiner_t5`

These statements are attributed to Keevash's 2014 existence theorem, but the
repository's `SteinerSystem` structure does not require `n > k` (nor
`k > t`), so the *degenerate* system on `n` points whose single block is the
whole ground set is an `S(t, n, n)` for every `n`: every `t`-subset is
contained in exactly one block, namely `univ`.  This yields infinitely many
Steiner systems with any fixed `t` — no Keevash needed.  (The intended
statements need a nondegeneracy hypothesis like `t < k < n`.)
-/

namespace SteinerSystems

/-- The degenerate Steiner system on `n` points whose only block is `univ`. -/
def trivialSystem (t n : ℕ) : SteinerSystem t n n where
  blocks := {Finset.univ}
  block_card := by simp
  cover_unique := fun R _ => by
    simp [Finset.filter_singleton, Finset.subset_univ]

/-- The map `n ↦ S(t, n, n)` packaged as a sigma-type element. -/
private def trivialFamily (t : ℕ) (n : ℕ) : Σ k n : ℕ, SteinerSystem t k n :=
  ⟨n, n, trivialSystem t n⟩

private lemma trivialFamily_injective (t : ℕ) : Function.Injective (trivialFamily t) :=
  fun _ _ hab => by simpa [trivialFamily] using congrArg Sigma.fst hab

/-- `infinitely_many_steiner_t4`, proved via degenerate systems. -/
theorem infinitely_many_steiner_t4' :
    ∃ S : Set (Σ k n : ℕ, SteinerSystem 4 k n), S.Infinite :=
  ⟨Set.range (trivialFamily 4), Set.infinite_range_of_injective (trivialFamily_injective 4)⟩

/-- `infinitely_many_steiner_t5`, proved via degenerate systems. -/
theorem infinitely_many_steiner_t5' :
    ∃ S : Set (Σ k n : ℕ, SteinerSystem 5 k n), S.Infinite :=
  ⟨Set.range (trivialFamily 5), Set.infinite_range_of_injective (trivialFamily_injective 5)⟩

end SteinerSystems
