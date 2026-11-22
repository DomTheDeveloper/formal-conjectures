import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow
import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin

theorem riemannHypothesis : RiemannHypothesis := by
  let row := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
  exact Claim.zeta <| UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin
    ⟨row, UpperTheory.Zero.LLC.recTExists, row⟩ (UpperTheory.One.vwin_of_row row)
