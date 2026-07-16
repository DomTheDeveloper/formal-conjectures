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
# Lévy convergence compatibility import

The pinned mathlib snapshot already provides Lévy's convergence theorem and the probability-measure
characteristic-function convergence API used by the standardized-binomial argument.  This module
keeps the project import path while delegating the proof to mathlib.
-/

public import Mathlib.MeasureTheory.Measure.LevyConvergence
