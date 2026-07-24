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

import FormalConjectures.GreensOpenProblems.Green14MaskDeepCubeCover

/-!
# Assembly combinators for the exact `W(3,20)` certificate tree

These theorems turn individually named LRAT leaf theorems into exhaustive
`Fin 8` and `Fin 64` families.  The final certificate file only has to supply
the appropriate leaf theorems as arguments.
-/

namespace Green14.CertificateAssembly

open Green14.MaskCubeCover
open Green14.MaskDeepCubeCover

/-- Assemble eight second-level leaf theorems into complete child coverage. -/
theorem all_child_masks (parent : Nat)
    (h0 : (grandchildCNFMask parent 0).Unsat)
    (h1 : (grandchildCNFMask parent 1).Unsat)
    (h2 : (grandchildCNFMask parent 2).Unsat)
    (h3 : (grandchildCNFMask parent 3).Unsat)
    (h4 : (grandchildCNFMask parent 4).Unsat)
    (h5 : (grandchildCNFMask parent 5).Unsat)
    (h6 : (grandchildCNFMask parent 6).Unsat)
    (h7 : (grandchildCNFMask parent 7).Unsat) :
    ∀ child : Fin 8, (grandchildCNFMask parent child.1).Unsat := by
  intro child
  fin_cases child <;> assumption

/-- Assemble eight third-level leaf theorems into complete third-level coverage. -/
theorem all_third_masks (parent child : Nat)
    (h0 : (greatGrandchildCNFMask parent child 0).Unsat)
    (h1 : (greatGrandchildCNFMask parent child 1).Unsat)
    (h2 : (greatGrandchildCNFMask parent child 2).Unsat)
    (h3 : (greatGrandchildCNFMask parent child 3).Unsat)
    (h4 : (greatGrandchildCNFMask parent child 4).Unsat)
    (h5 : (greatGrandchildCNFMask parent child 5).Unsat)
    (h6 : (greatGrandchildCNFMask parent child 6).Unsat)
    (h7 : (greatGrandchildCNFMask parent child 7).Unsat) :
    ∀ third : Fin 8,
      (greatGrandchildCNFMask parent child third.1).Unsat := by
  intro third
  fin_cases third <;> assumption

/-- Eight third-level certificates close one hard grandchild. -/
theorem grandchild_of_eight_thirds (parent child : Nat)
    (h0 : (greatGrandchildCNFMask parent child 0).Unsat)
    (h1 : (greatGrandchildCNFMask parent child 1).Unsat)
    (h2 : (greatGrandchildCNFMask parent child 2).Unsat)
    (h3 : (greatGrandchildCNFMask parent child 3).Unsat)
    (h4 : (greatGrandchildCNFMask parent child 4).Unsat)
    (h5 : (greatGrandchildCNFMask parent child 5).Unsat)
    (h6 : (greatGrandchildCNFMask parent child 6).Unsat)
    (h7 : (greatGrandchildCNFMask parent child 7).Unsat) :
    (grandchildCNFMask parent child).Unsat := by
  exact grandchildCNFMask_unsat_of_all_third_masks parent child
    (all_third_masks parent child h0 h1 h2 h3 h4 h5 h6 h7)

/-- Eight second-level certificates close one hard first-level parent. -/
theorem parent_of_eight_children (parent : Nat)
    (h0 : (grandchildCNFMask parent 0).Unsat)
    (h1 : (grandchildCNFMask parent 1).Unsat)
    (h2 : (grandchildCNFMask parent 2).Unsat)
    (h3 : (grandchildCNFMask parent 3).Unsat)
    (h4 : (grandchildCNFMask parent 4).Unsat)
    (h5 : (grandchildCNFMask parent 5).Unsat)
    (h6 : (grandchildCNFMask parent 6).Unsat)
    (h7 : (grandchildCNFMask parent 7).Unsat) :
    (cubeCNFMask parent).Unsat := by
  exact cubeCNFMask_unsat_of_all_child_masks parent
    (all_child_masks parent h0 h1 h2 h3 h4 h5 h6 h7)

/-- Assemble all 64 externally numbered first-level certificates. -/
theorem all_parent_masks
    (h00 : (cubeCNFMask 0).Unsat) (h01 : (cubeCNFMask 1).Unsat)
    (h02 : (cubeCNFMask 2).Unsat) (h03 : (cubeCNFMask 3).Unsat)
    (h04 : (cubeCNFMask 4).Unsat) (h05 : (cubeCNFMask 5).Unsat)
    (h06 : (cubeCNFMask 6).Unsat) (h07 : (cubeCNFMask 7).Unsat)
    (h08 : (cubeCNFMask 8).Unsat) (h09 : (cubeCNFMask 9).Unsat)
    (h10 : (cubeCNFMask 10).Unsat) (h11 : (cubeCNFMask 11).Unsat)
    (h12 : (cubeCNFMask 12).Unsat) (h13 : (cubeCNFMask 13).Unsat)
    (h14 : (cubeCNFMask 14).Unsat) (h15 : (cubeCNFMask 15).Unsat)
    (h16 : (cubeCNFMask 16).Unsat) (h17 : (cubeCNFMask 17).Unsat)
    (h18 : (cubeCNFMask 18).Unsat) (h19 : (cubeCNFMask 19).Unsat)
    (h20 : (cubeCNFMask 20).Unsat) (h21 : (cubeCNFMask 21).Unsat)
    (h22 : (cubeCNFMask 22).Unsat) (h23 : (cubeCNFMask 23).Unsat)
    (h24 : (cubeCNFMask 24).Unsat) (h25 : (cubeCNFMask 25).Unsat)
    (h26 : (cubeCNFMask 26).Unsat) (h27 : (cubeCNFMask 27).Unsat)
    (h28 : (cubeCNFMask 28).Unsat) (h29 : (cubeCNFMask 29).Unsat)
    (h30 : (cubeCNFMask 30).Unsat) (h31 : (cubeCNFMask 31).Unsat)
    (h32 : (cubeCNFMask 32).Unsat) (h33 : (cubeCNFMask 33).Unsat)
    (h34 : (cubeCNFMask 34).Unsat) (h35 : (cubeCNFMask 35).Unsat)
    (h36 : (cubeCNFMask 36).Unsat) (h37 : (cubeCNFMask 37).Unsat)
    (h38 : (cubeCNFMask 38).Unsat) (h39 : (cubeCNFMask 39).Unsat)
    (h40 : (cubeCNFMask 40).Unsat) (h41 : (cubeCNFMask 41).Unsat)
    (h42 : (cubeCNFMask 42).Unsat) (h43 : (cubeCNFMask 43).Unsat)
    (h44 : (cubeCNFMask 44).Unsat) (h45 : (cubeCNFMask 45).Unsat)
    (h46 : (cubeCNFMask 46).Unsat) (h47 : (cubeCNFMask 47).Unsat)
    (h48 : (cubeCNFMask 48).Unsat) (h49 : (cubeCNFMask 49).Unsat)
    (h50 : (cubeCNFMask 50).Unsat) (h51 : (cubeCNFMask 51).Unsat)
    (h52 : (cubeCNFMask 52).Unsat) (h53 : (cubeCNFMask 53).Unsat)
    (h54 : (cubeCNFMask 54).Unsat) (h55 : (cubeCNFMask 55).Unsat)
    (h56 : (cubeCNFMask 56).Unsat) (h57 : (cubeCNFMask 57).Unsat)
    (h58 : (cubeCNFMask 58).Unsat) (h59 : (cubeCNFMask 59).Unsat)
    (h60 : (cubeCNFMask 60).Unsat) (h61 : (cubeCNFMask 61).Unsat)
    (h62 : (cubeCNFMask 62).Unsat) (h63 : (cubeCNFMask 63).Unsat) :
    ∀ mask : Fin 64, (cubeCNFMask mask.1).Unsat := by
  intro mask
  fin_cases mask <;> assumption

/-- Sixty-four first-level certificates prove the exact value `W(3,20)=389`. -/
theorem exact_of_sixty_four_parents
    (h00 : (cubeCNFMask 0).Unsat) (h01 : (cubeCNFMask 1).Unsat)
    (h02 : (cubeCNFMask 2).Unsat) (h03 : (cubeCNFMask 3).Unsat)
    (h04 : (cubeCNFMask 4).Unsat) (h05 : (cubeCNFMask 5).Unsat)
    (h06 : (cubeCNFMask 6).Unsat) (h07 : (cubeCNFMask 7).Unsat)
    (h08 : (cubeCNFMask 8).Unsat) (h09 : (cubeCNFMask 9).Unsat)
    (h10 : (cubeCNFMask 10).Unsat) (h11 : (cubeCNFMask 11).Unsat)
    (h12 : (cubeCNFMask 12).Unsat) (h13 : (cubeCNFMask 13).Unsat)
    (h14 : (cubeCNFMask 14).Unsat) (h15 : (cubeCNFMask 15).Unsat)
    (h16 : (cubeCNFMask 16).Unsat) (h17 : (cubeCNFMask 17).Unsat)
    (h18 : (cubeCNFMask 18).Unsat) (h19 : (cubeCNFMask 19).Unsat)
    (h20 : (cubeCNFMask 20).Unsat) (h21 : (cubeCNFMask 21).Unsat)
    (h22 : (cubeCNFMask 22).Unsat) (h23 : (cubeCNFMask 23).Unsat)
    (h24 : (cubeCNFMask 24).Unsat) (h25 : (cubeCNFMask 25).Unsat)
    (h26 : (cubeCNFMask 26).Unsat) (h27 : (cubeCNFMask 27).Unsat)
    (h28 : (cubeCNFMask 28).Unsat) (h29 : (cubeCNFMask 29).Unsat)
    (h30 : (cubeCNFMask 30).Unsat) (h31 : (cubeCNFMask 31).Unsat)
    (h32 : (cubeCNFMask 32).Unsat) (h33 : (cubeCNFMask 33).Unsat)
    (h34 : (cubeCNFMask 34).Unsat) (h35 : (cubeCNFMask 35).Unsat)
    (h36 : (cubeCNFMask 36).Unsat) (h37 : (cubeCNFMask 37).Unsat)
    (h38 : (cubeCNFMask 38).Unsat) (h39 : (cubeCNFMask 39).Unsat)
    (h40 : (cubeCNFMask 40).Unsat) (h41 : (cubeCNFMask 41).Unsat)
    (h42 : (cubeCNFMask 42).Unsat) (h43 : (cubeCNFMask 43).Unsat)
    (h44 : (cubeCNFMask 44).Unsat) (h45 : (cubeCNFMask 45).Unsat)
    (h46 : (cubeCNFMask 46).Unsat) (h47 : (cubeCNFMask 47).Unsat)
    (h48 : (cubeCNFMask 48).Unsat) (h49 : (cubeCNFMask 49).Unsat)
    (h50 : (cubeCNFMask 50).Unsat) (h51 : (cubeCNFMask 51).Unsat)
    (h52 : (cubeCNFMask 52).Unsat) (h53 : (cubeCNFMask 53).Unsat)
    (h54 : (cubeCNFMask 54).Unsat) (h55 : (cubeCNFMask 55).Unsat)
    (h56 : (cubeCNFMask 56).Unsat) (h57 : (cubeCNFMask 57).Unsat)
    (h58 : (cubeCNFMask 58).Unsat) (h59 : (cubeCNFMask 59).Unsat)
    (h60 : (cubeCNFMask 60).Unsat) (h61 : (cubeCNFMask 61).Unsat)
    (h62 : (cubeCNFMask 62).Unsat) (h63 : (cubeCNFMask 63).Unsat) :
    Green14.W 3 20 = 389 := by
  exact W_3_20_eq_389_of_all_masks
    (all_parent_masks h00 h01 h02 h03 h04 h05 h06 h07
      h08 h09 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
      h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39
      h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50 h51 h52 h53 h54 h55
      h56 h57 h58 h59 h60 h61 h62 h63)

end Green14.CertificateAssembly
