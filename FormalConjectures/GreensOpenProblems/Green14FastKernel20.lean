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

public import FormalConjectures.GreensOpenProblems.Green14Core

/-!
# Fast kernel audit for the Green14 t=20 certificate

This audit module stores the coloring directly as a Boolean array and enumerates
only positive differences whose final progression term remains in bounds.  The
certificate theorem is proved by kernel `decide`; no native evaluator is used.
-/

public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Green14.FastKernel

private def colors20 : Array Bool :=
  #[
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false,
    true, true, true, true, false, true, true, true, true, true, true, true, false, true, false, true,
    true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true,
    true, false, true, true, true, true, true, true, true, true, true, false, true, true, true, true,
    false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, false, false, true, true, true, false, false, true, false, true, true, true, true, true, true,
    true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true,
    false, true, true, true, true, false, true, false, true, true, true, true, true, false, true, true,
    true, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true,
    true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true,
    true, true, false, true, true, true, false, true, true, true, true, true, false, true, false, true,
    true, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    false, true, true, true, true, true, true, true, true, true, false, true, false, false, true, true,
    true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, false, true, false, true, true, true, true, false, true, true, true, true, true, true, true,
    true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true,
    false, true, true, true, true, false, true, false, true, true, true, true, true, true, true, false,
    true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true,
    false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true
  ]

private def colorAt (colors : Array Bool) (i : Nat) : Bool :=
  colors[i]!

private def hasAP (N k : Nat) (colors : Array Bool) (color : Bool) : Bool :=
  (List.range N).any fun a =>
    (List.range ((N - 1 - a) / (k - 1))).any fun d0 =>
      let d := d0 + 1
      (List.range k).all fun i => colorAt colors (a + i * d) == color

theorem valid_20 :
    hasAP 388 3 colors20 false = false ∧
      hasAP 388 20 colors20 true = false := by
  decide

#print axioms Green14.FastKernel.valid_20

end Green14.FastKernel
