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

import FormalConjectures.ErdosProblems.«142»
import FormalConjectures.ErdosProblems.«272»
import FormalConjectures.ErdosProblems.«321»
import FormalConjectures.ErdosProblems.«340»
import FormalConjectures.ErdosProblems.«357»
import FormalConjectures.ErdosProblems.«409»
import FormalConjectures.ErdosProblems.«422»
import FormalConjectures.ErdosProblems.«507»
import FormalConjectures.ErdosProblems.«539»
import FormalConjectures.ErdosProblems.«688»
import FormalConjectures.ErdosProblems.«789»
import FormalConjectures.GreensOpenProblems.«27»
import FormalConjectures.GreensOpenProblems.«37»

/-!
# The reflexive-answer degeneracy class

25 `research open` statements in the repository ask for a growth estimate in
the form `f =O[l] answer(sorry)`, `f =Θ[l] answer(sorry)`, or
`f ~[l] answer(sorry)` (in some cases with the answer on the left).  All three
relations are *reflexive*, so each statement is formally resolved by
instantiating the answer with the estimated function itself — no mathematics
required.  This file proves all 25, each with the original statement verbatim
and `answer(sorry)` replaced by the left-hand side.

These "solutions" are of course worthless as mathematics: the point is that
the `answer( )` form used for asymptotic-estimate questions does not constrain
the answer to be a *closed form* (or even to be different from the function
being estimated), so the formal statements do not capture the open problems.
A fix could require the answer to be built from a fixed vocabulary of
elementary functions, or state the problems as specific-conjecture variants.

(`erdos_361.bigO/.bigTheta` also belong to this class but are already resolved
by their contradictory hypothesis; see `Erdos361_15.lean`.)
-/

set_option linter.unusedTactic false
set_option linter.tacticAnalysis.neverExecuted false

open Filter Asymptotics Finset Real
open scoped Topology ArithmeticFunction.sigma Nat Pointwise

namespace Green37

theorem green_37_theta_answered (k : ℕ) :
    (fun N ↦ (m N k : ℝ)) =Θ[atTop] (((fun N ↦ (m N k : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Green37

namespace Green37

theorem green_37_bigO_answered (k : ℕ) :
    (fun N ↦ (m N k : ℝ)) =O[atTop] (((fun N ↦ (m N k : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Green37

namespace Green27

theorem green_27_equivalent_answered :
  ((m) : ℕ → ℝ) ~[primesAtTop] m := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Green27

namespace Erdos142

theorem erdos_142_answered (k : ℕ) : (fun N => (r k N : ℝ)) =Θ[atTop] (((fun N => (r k N : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos142

namespace Erdos142

theorem erdos_142_variants_three_answered : (fun N => (r 3 N : ℝ)) =Θ[atTop] (((fun N => (r 3 N : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos142

namespace Erdos357

theorem erdos_357_parts_ii_bigO_version_answered :
    (((fun n ↦ (f n : ℝ))) : ℕ → ℝ) =O[atTop] (fun n ↦ (f n : ℝ)) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos357

namespace Erdos357

theorem erdos_357_parts_ii_bigO_version_symm_answered :
    (fun n ↦ (f n : ℝ)) =O[atTop] (((fun n ↦ (f n : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos357

namespace Erdos357

theorem erdos_357_parts_ii_bigTheta_version_answered :
    (fun n ↦ (f n : ℝ)) =Θ[atTop] (((fun n ↦ (f n : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos357

namespace Erdos357

theorem erdos_357_variants_monotone_parts_ii_bigO_version_answered :
    (((fun n ↦ (h n : ℝ))) : ℕ → ℝ) =O[atTop] (fun n ↦ (h n : ℝ)) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos357

namespace Erdos357

theorem erdos_357_variants_monotone_parts_ii_bigO_version_symm_answered :
    (fun n ↦ (h n : ℝ)) =O[atTop] (((fun n ↦ (h n : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos357

namespace Erdos357

theorem erdos_357_variants_monotone_parts_ii_bigTheta_version_answered :
    (fun n ↦ (h n : ℝ)) =Θ[atTop] (((fun n ↦ (h n : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos357

namespace Erdos272

theorem erdos_272_answered :
    (fun N ↦ (maxArithInterCard N : ℝ)) ~[atTop] (((fun N ↦ (maxArithInterCard N : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos272

namespace Erdos539

theorem erdos_539_answered :
    (fun n ↦ (cofactorThreshold n : ℝ)) =Θ[atTop] (((fun n ↦ (cofactorThreshold n : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos539

namespace Erdos688

theorem erdos_688_parts_i_lower_bound_answered :
    ((epsilonFunction) : ℕ → ℝ) =O[atTop] epsilonFunction := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos688

namespace Erdos688

theorem erdos_688_parts_i_upper_bound_answered :
    epsilonFunction =O[atTop] ((epsilonFunction) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos688

namespace Erdos507

theorem erdos_507_equivalent_answered:
    α ~[atTop] ((α) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos507

namespace Erdos789

theorem erdos_789_answered :
    (fun n ↦ (subsetSumThreshold n : ℝ)) =Θ[atTop] (((fun n ↦ (subsetSumThreshold n : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos789

namespace Erdos340

theorem erdos_340_variants_isTheta_answered (ε : ℝ) (hε : ε > 0) :
    (fun n : ℕ ↦ ((Set.range greedySidon ∩ Set.Icc 1 n).ncard : ℝ)) =Θ[atTop]
      (((fun n : ℕ ↦ ((Set.range greedySidon ∩ Set.Icc 1 n).ncard : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos340

namespace Erdos409

theorem erdos_409_parts_i_isTheta_answered (c : ℕ → ℕ)
    (h : ∀ n > 0, IsLeast { i | (φ · + 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =Θ[atTop] (((fun n => (c n : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos409

namespace Erdos409

theorem erdos_409_parts_i_isBigO_answered (c : ℕ → ℕ)
    (h : ∀ n > 0, IsLeast { i | (φ · + 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =O[atTop] (((fun n => (c n : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos409

namespace Erdos409

theorem erdos_409_variants_sigma_isTheta_answered (c : ℕ → ℕ)
    (h : ∀ n > 1, IsLeast { i | (σ 1 · - 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =Θ[atTop] (((fun n => (c n : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos409

namespace Erdos409

theorem erdos_409_variants_sigma_isBigO_answered (c : ℕ → ℕ)
    (h : ∀ n > 1, IsLeast { i | (σ 1 · - 1)^[i] n |>.Prime } (c n)) :
    (fun n => (c n : ℝ)) =O[atTop] (((fun n => (c n : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos409

namespace Erdos321

theorem erdos_321_variants_isTheta_answered :
    (fun N ↦ (R N : ℝ)) =Θ[atTop] (((fun N ↦ (R N : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos321

namespace Erdos321

theorem erdos_321_variants_isBigO_answered :
    (fun N ↦ (R N : ℝ)) =O[atTop] (((fun N ↦ (R N : ℝ))) : ℕ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos321

namespace Erdos422

theorem erdos_422_variants_growth_rate_answered :
    (fun n ↦ (f n : ℝ)) =O[atTop] (((fun n ↦ (f n : ℝ))) : ℕ+ → ℝ) := by
  first
  | exact Asymptotics.isBigO_refl _ _
  | exact Asymptotics.isTheta_refl _ _
  | exact Asymptotics.IsEquivalent.refl

end Erdos422
