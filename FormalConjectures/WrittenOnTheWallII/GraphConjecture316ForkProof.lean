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

import FormalConjectures.WrittenOnTheWallII.GraphConjecture316
import WOWII.WotW316Final

namespace WrittenOnTheWallII.GraphConjecture316

open SimpleGraph

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Fork-hosted exact Lean proof of WOWII Graph Conjecture 316. -/
theorem conjecture316_fork_proof (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card) :
    IsWellTotallyDominated G := by
  exact conjecture316_solved G hG h

#print axioms conjecture316_fork_proof

end WrittenOnTheWallII.GraphConjecture316
