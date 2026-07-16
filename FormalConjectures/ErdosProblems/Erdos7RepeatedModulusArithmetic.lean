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

import Mathlib

/-!
# Exact arithmetic endpoints for repeated-modulus obstructions in Erdős Problem 7

These are the final rational inequalities produced by independently checkable
finite certificates for the square-free `τ₃ = 2` reduction. The combinatorial
probability lemmas and certificate verifiers are separate; this file deliberately
does not claim `Erdos7.erdos_7`.
-/

namespace Erdos7RepeatedModulusArithmetic

/-- Exact Hunter spanning-forest upper bound for ten auxiliary primes. -/
theorem ten_auxiliary_forest_gap :
    (7969121746 : ℚ) / 8071457625 < 1 := by
  norm_num

/-- Rebuilt exact sequential Bonferroni/KAT upper bound for eleven auxiliary primes. -/
theorem eleven_auxiliary_sequential_gap :
    (111032504349593270518862 : ℚ) /
      111170394697317561230625 < 1 := by
  norm_num

/-- Exact uncovered density guaranteed by the rebuilt eleven-prime certificate. -/
theorem eleven_auxiliary_uncovered_margin :
    (1 : ℚ) -
        (111032504349593270518862 : ℚ) /
          111170394697317561230625 =
      (137890347724290711763 : ℚ) /
        111170394697317561230625 := by
  norm_num

end Erdos7RepeatedModulusArithmetic
