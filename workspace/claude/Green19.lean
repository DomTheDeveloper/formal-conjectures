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

import FormalConjectures.GreensOpenProblems.«19»

/-!
# `green_19.lower` and `green_19.upper` are not open problems

`FormalConjectures/GreensOpenProblems/19.lean` contains three statements about
the same constant `C` (the infimum of the valid corner-counting exponents):

* `green_19 : C = 4`, tagged **`research solved`**, with the docstring
  "This question has been resolved by [FSS20], showing that `C = 4`";
* `green_19.lower : C >= 3.13`, tagged **`research open`**;
* `green_19.upper : C <= 4`, tagged **`research open`**.

But `C = 4` implies both `C ≥ 3.13` and `C ≤ 4` immediately, so neither
variant can be open once the main statement is recorded as solved.  (The
docstrings themselves attribute both bounds to [Ma21], which likewise
indicates they are theorems, not conjectures.)

This file proves both implications, sorry-free.  Since `green_19` itself is
`sorry`-ed in the repository, the results are stated as implications from its
statement rather than as unconditional facts — which is exactly the point:
no *new* mathematics stands between the solved statement and these two.

The fix is editorial: retag `green_19.lower` and `green_19.upper` as
`research solved` (or derive them from `green_19`).
-/

namespace Green19Resolution

open Green19

/-- `green_19.lower` follows immediately from the `research solved` statement
`green_19 : C = 4`. -/
theorem lower_of_green_19 (h : C = 4) : C ≥ 3.13 := by
  rw [h]
  norm_num

/-- `green_19.upper` follows immediately from the `research solved` statement
`green_19 : C = 4`. -/
theorem upper_of_green_19 (h : C = 4) : C ≤ 4 := le_of_eq h

/-- Both "open" variants at once. -/
theorem lower_and_upper_of_green_19 (h : C = 4) : C ≥ 3.13 ∧ C ≤ 4 :=
  ⟨lower_of_green_19 h, upper_of_green_19 h⟩

end Green19Resolution
