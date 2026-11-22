import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow
import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin
import Statements

open UpperTheory in
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := by
  let row := Gal.Int.galoisLocalGlobalStrong_recParameter
  exact LiteratureTheorems.every_character_of_literature_of_vWin
    ⟨row, Zero.LLC.recTExists, row⟩ (One.vwin_of_row row)

theorem riemannHypothesis : RiemannHypothesis := Claim.zeta LFunction_ne_zero_of_half_lt_re
theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := riemannHypothesis
theorem LFunction_eq_zero_re : DirichletLZerosOnLine := Claim.strip LFunction_ne_zero_of_half_lt_re
theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine :=
  fun N _ χ _ => LFunction_eq_zero_re N χ
