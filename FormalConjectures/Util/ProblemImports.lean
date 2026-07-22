/-
Copyright 2025 The Formal Conjectures Authors.

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

public import Mathlib
public import FormalConjectures.Util.Answer
public import FormalConjectures.Util.Linters.AMSLinter
public import FormalConjectures.Util.Linters.AnswerLinter
public import FormalConjectures.Util.Linters.CategoryDocstringLinter
public import FormalConjectures.Util.Linters.CategoryLinter
public import FormalConjectures.Util.Linters.CopyrightLinter
public import FormalConjectures.Util.Linters.ExistsImplicationLinter
public import FormalConjectures.Util.Linters.ModuleDocstringLinter
public import FormalConjectures.Util.Linters.NamespaceLinter

/-!
# Standard imports for the frozen OEIS A263135 proof audit

This audit prelude provides Mathlib and the standard Formal Conjectures
attributes and linters. The project-wide `FormalConjecturesForMathlib`
aggregator is intentionally omitted because the A263135 statement and proof
do not use it.
-/
