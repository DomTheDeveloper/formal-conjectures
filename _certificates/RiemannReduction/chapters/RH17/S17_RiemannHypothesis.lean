import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc
import RH17.S09_Reflection
import RH17.S16_TwoArithmeticInputs

/-! # 17. Ordinary RH
The first theorem isolates the arithmetic inputs. The second constructs them
from the published theory and concludes Mathlib's `RiemannHypothesis`. -/

namespace RH17

theorem riemannHypothesisOfArithmetic
    (chains : UpperTheory.Top.TopG) (cohomology : ZetaCohomology) :
    RiemannHypothesis :=
  rhOfPowerWindows (by norm_num) (primeWindowsOfArithmetic chains cohomology)

#print axioms riemannHypothesisOfArithmetic

open UpperTheory.LiteratureTheorems

/-- Connect the archived providers to the specialized ordinary-RH deduction. -/
theorem riemannHypothesisFromPublishedArithmetic : RiemannHypothesis := by
  let row := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  let O : OpenLiteratureStatements :=
    ⟨row, UpperTheory.Zero.LLC.recTExists, row⟩
  let P := published_results_eigen O
  let F := published_results_first O
  let matching := theta_integrals_agree_and_local_matching_of_literature O
  let hX := SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt
    (resolution_char_zero_of_literature O)
    (principalisation_char_zero_of_literature O)
    (poincare_lelong_inv_of_literature O)
    PositivityTheory.Pf1.HilbertSamuelMoriwaki.hsUse_outright
    PositivityTheory.Pf1.HilbertSamuelMoriwaki.moriwakiBig_outright
    (fargues_exact_of_literature O)
    (zarhin_statement O)
    (nef_rr_of_literature O)
    (siegel_toroidal_integral_of_literature O)
    (toroidal_for_fan_ks_of_literature O)
    (semi_abelian_lie_seminegative_of_literature O)
    (point_separation_pair_of_literature O)
    (ar_degree_of_literature O)
    (published_results_arithmetic O)
    (grothendieck_deformation_of_literature O)
  let hL := local_langlands_gl_recT_exists_of_literature O
  let green := GlobalTheory.GreenBridge.green_of_regular
    (GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses.greenRegularCharacters P)
  obtain ⟨geometry⟩ := UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound
    P F matching.1 matching.2 hX hL (fun cDep => UpperTheory.N.boundAtTwoThree_linked_of_recT
      (GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses.nLink P)
      (GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep))
  have chains : UpperTheory.Top.TopG := GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _
    (UpperTheory.Top.shape_closed_link_n_of_green green) trivial trivial geometry
  exact riemannHypothesisOfArithmetic chains (UpperTheory.One.vwin_of_row row Formalism.HC.PChar.one)

#print axioms riemannHypothesisFromPublishedArithmetic

end RH17
