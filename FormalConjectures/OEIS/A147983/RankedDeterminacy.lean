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

import FormalConjectures.OEIS.A147983.KernelCertificate

/-!
# Determinacy of progressively bounded normal-play games
-/

namespace OeisA147983.KernelCertificate
namespace RankedGame

variable {P : Type} (G : RankedGame P)

/-- Every position in a progressively bounded normal-play game is losing or winning. -/
theorem outcome_exists (p : P) :
    Nonempty (Outcome G.Move p false) ∨ Nonempty (Outcome G.Move p true) := by
  classical
  have all : ∀ k : ℕ, ∀ p : P, G.rank p = k →
      Nonempty (Outcome G.Move p false) ∨ Nonempty (Outcome G.Move p true) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro p hrank
        by_cases hchildren : ∀ q : P, G.Move p q → Nonempty (Outcome G.Move q true)
        · exact Or.inl ⟨Outcome.losing (fun q hq ↦ (hchildren q hq).some)⟩
        · push_neg at hchildren
          obtain ⟨q, hmove, hnotwin⟩ := hchildren
          have hlt : G.rank q < k := by
            simpa [← hrank] using G.decreases hmove
          rcases ih _ hlt q rfl with hlose | hwin
          · exact Or.inr ⟨Outcome.winning hmove hlose.some⟩
          · exact False.elim (hnotwin hwin)
  exact all _ p rfl

/-- A position cannot be both losing and winning. -/
theorem outcome_exclusive {p : P} (hlose : Outcome G.Move p false)
    (hwin : Outcome G.Move p true) : False := by
  have all : ∀ k : ℕ, ∀ p : P, G.rank p = k →
      Outcome G.Move p false → Outcome G.Move p true → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro p hrank hpLose hpWin
        cases hpLose with
        | losing children =>
            cases hpWin with
            | winning move child =>
                have hlt : G.rank _ < k := by
                  simpa [← hrank] using G.decreases move
                exact ih _ hlt _ rfl child (children _ move)
  exact all _ p rfl hlose hwin

/-- The losing and winning classifications are disjoint. -/
theorem not_isLosing_and_isWinning {p : P} :
    ¬(IsLosing G.Move p ∧ IsWinning G.Move p) := by
  rintro ⟨⟨hlose⟩, ⟨hwin⟩⟩
  exact G.outcome_exclusive hlose hwin

end RankedGame
end OeisA147983.KernelCertificate
