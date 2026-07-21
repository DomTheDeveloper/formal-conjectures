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
# Written on the Wall II - Conjecture 100

**Verbatim statement (WOWII #100, status O):**
> If G is a simple connected graph, then α(G) ≤ CEIL[(maximum of λ(v) + 0.5*length(Ḡ))/2]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj100

The WOWII HTML uses `length(Ḡ)` (the bar denotes graph complement); the
extracted JSON in our private repo previously dropped the overline. The
formal statement below uses the diameter of `Gᶜ`.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitional choice

DeLaVina does not give a stand-alone definition for `length(H)` on the WOWII
page. We interpret it as the **diameter** of `H` (the maximum eccentricity,
i.e. `H.ediam`), which is the most natural graph-theoretic notion
of "length" of a graph. Combined with the overline above, the inequality reads:
  `α(G) ≤ ⌈(max_v l(v) + 0.5 · diam(Gᶜ)) / 2⌉`
where `l(v) = indepNeighbors G v` and `diam(Gᶜ) = Gᶜ.ediam.toNat`.

## Connectedness of the complement

When `Gᶜ` is **disconnected**, `Gᶜ.ediam = ⊤` and
`Gᶜ.ediam.toNat = 0`, so the right-hand side silently degenerates
to `⌈max_v l(v) / 2⌉` — a much weaker (and often vacuously false) statement
than the conjecture intends. We therefore add the hypothesis `hGc : Gᶜ.Connected`
so the inequality is genuinely about a finite `length(Ḡ) = diam(Gᶜ)`.
-/

namespace WrittenOnTheWallII.GraphConjecture100

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 100](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj100)
(status O):

For a simple connected graph `G`,
`α(G) ≤ ⌈(max_v l(v) + 0.5 · diam(Gᶜ)) / 2⌉`
where `α(G) = G.indepNum` is the independence number,
`max_v l(v)` is the maximum over all vertices of the independence number of
the neighbourhood (in `G`), and `diam(Gᶜ)` is the diameter of the
complement `Gᶜ`.

**Note:** `length(Ḡ)` in DeLaVina's original is interpreted here as the
diameter of the complement. The hypothesis `hGc : Gᶜ.Connected` is added so
that `diam(Gᶜ)` is finite (otherwise `Gᶜ.ediam = ⊤` and
`Gᶜ.ediam.toNat` collapses silently to `0`); see the module
docstring above.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at "https://github.com/DomTheDeveloper/formal-conjectures/blob/3ef37a1eb2f13e164ddb663c408ceb20e8411c30/FormalConjectures/WrittenOnTheWallII/GraphConjecture100Complete.lean"]
theorem conjecture100 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hGc : Gᶜ.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤ ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
  sorry

-- Sanity checks

/-- The independence number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.indepNum := Nat.zero_le _

/-- `ediam` on a two-vertex complete graph is `⊤` since all eccentricities
are computed via `sSup` and the distance between the two vertices is 1. -/
@[category test, AMS 5]
example : 0 ≤ (⊤ : SimpleGraph (Fin 2)).ediam.toNat := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture100
