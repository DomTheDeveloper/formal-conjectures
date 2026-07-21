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

import WOWII.ZZGraphConjecture314Final

/-!
# Written on the Wall II - Conjecture 314

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

open Classical

namespace WrittenOnTheWallII.GraphConjecture314

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
WOWII [Conjecture 314](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj314):

For every finite simple connected graph $G$ with $n > 1$ vertices,
if $G$ is triangle-free and $\mathrm{path}(G) \le 4$, then $G$ is well totally
dominated.

Here $\mathrm{path}(G) = \mathrm{largestInducedPathSize}\, G$ is the **size of a
largest induced path** in $G$, defined in `GraphConjecture314Core`.

**Disambiguation.** Earlier revisions of this file used the `SimpleGraph.path`
invariant, but that is the *floor of the average distance*, not the size of a
largest induced path — a different quantity that makes Conjecture 314 vacuous
in many cases.
-/
@[category research solved, AMS 5]
theorem conjecture314 [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4) :
    IsWellTotallyDominated G := by
  exact conjecture314_proved G hG hTriFree hPath

-- Sanity checks

/-- The complete graph $K_3$ has a triangle. -/
@[category test, AMS 5]
example : ∃ a b c : Fin 3, (⊤ : SimpleGraph (Fin 3)).Adj a b ∧
    (⊤ : SimpleGraph (Fin 3)).Adj b c ∧ (⊤ : SimpleGraph (Fin 3)).Adj c a := by
  exact ⟨0, 1, 2, by decide, by decide, by decide⟩

/-- `largestInducedPathSize G` is nonnegative. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] :
    0 ≤ largestInducedPathSize G := Nat.zero_le _

#print axioms WrittenOnTheWallII.GraphConjecture314.conjecture314

end WrittenOnTheWallII.GraphConjecture314
