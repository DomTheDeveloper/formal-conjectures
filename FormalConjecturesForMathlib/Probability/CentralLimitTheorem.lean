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
module

/-!
# Central limit theorem compatibility import

The pinned mathlib snapshot already contains the one-dimensional central limit theorem and the exact
`tendsto_charFun_inv_sqrt_mul_pow` lemma needed for the standardized-binomial proof.  This module
preserves the existing project import path without maintaining a duplicate proof.
-/

public import Mathlib.Probability.CentralLimitTheorem
