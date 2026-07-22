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
# Sylver Coinage: odd replies to the opening move 16

Hutchings proved that a two-move Sylver Coinage position `{m, n}`, where `m` and `n` are greater
than one and coprime, is an ender. Except for the special position `{2, 3}`, such a position is an
N-position: the player whose turn comes next has a winning strategy.

After the opening move `16` and a nonterminal odd reply `q > 1`, it is the original first player's
turn. Since an odd `q` is coprime to `16`, Hutchings's theorem implies that `{16, q}` is an
N-position. Therefore every odd reply greater than one loses for the replying player. The remaining
odd reply `q = 1` loses immediately by the defining rule of Sylver Coinage.

This file formalizes only the nonterminal specialization of Hutchings's theorem. It does not
formalize the full game semantics, prove Hutchings's theorem itself, or determine the still-open
value `A248380(16)`.

*References:*
- [OEIS A248380](https://oeis.org/A248380)
- George Sicherman, ["Theory and Practice of Sylver Coinage"]
  (https://math.colgate.edu/~integers/cg2/cg2.pdf), *INTEGERS* **2** (2002), #G02.
-/

namespace SylverCoinageOddReply

/--
The conclusion of Hutchings's two-generator theorem, abstracted over the predicate expressing
that a finite Sylver Coinage position is an N-position.
-/
def HutchingsTwoGeneratorConclusion (isNPosition : Finset ℕ → Prop) : Prop :=
  ∀ m n : ℕ,
    1 < m →
    1 < n →
    Nat.Coprime m n →
    ({m, n} : Finset ℕ) ≠ {2, 3} →
    isNPosition {m, n}

/-- Every odd natural number is coprime to `16`. -/
@[category test, AMS 11]
theorem coprime_sixteen_of_odd (q : ℕ) (hq : Odd q) : Nat.Coprime 16 q := by
  simpa using Nat.Coprime.pow_left 4 hq.coprime_two_left

/--
Assuming Hutchings's two-generator theorem, every nonterminal odd reply `q > 1` to an opening move
of `16` leaves an N-position for the original first player. Thus the reply loses for the replying
player. The terminal reply `q = 1` is handled directly by the rule that naming `1` loses.
-/
@[category research solved, AMS 91]
theorem nonterminal_odd_reply_is_n_position
    (isNPosition : Finset ℕ → Prop)
    (hHutchings : HutchingsTwoGeneratorConclusion isNPosition)
    (q : ℕ) (hq_one : 1 < q) (hq : Odd q) :
    isNPosition {16, q} := by
  apply hHutchings 16 q (by norm_num) hq_one (coprime_sixteen_of_odd q hq)
  intro h
  have hmem : 16 ∈ ({2, 3} : Finset ℕ) := by
    rw [← h]
    simp
  norm_num at hmem

end SylverCoinageOddReply
