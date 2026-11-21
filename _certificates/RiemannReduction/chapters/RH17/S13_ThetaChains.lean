import RH17.S12_HostFields
import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG

/-! # 13. Extract the chain estimate needed for zeta
`TopG` is the archive's arithmetic supply theorem stated as a proposition.
Applied at width 3/2 to the modulus-one request, it produces families carrying
chains of theta lifts. A slope comparison weighs divisibility at finite places
against sizes at infinite places. The constants governing the losses must be
fixed before the small exponent ε is chosen. -/

namespace RH17

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC UpperTheory.Top GlobalTheory.EX

abbrev ZetaChains := FamilyClassConnected ((GChi PChar.one).cls (3/2))

abbrev ZetaTiedWindows := ChebyshevInequalityAtWindowScale (Fam := FamP)
  (fun Fm => Fm.toFamCore) (fun Fm => ChainTied Fm) (3/2) (Level.cyc PChar.one)

theorem chainsOfHosts (supply : TopG) (hosts : ZetaHosts) : ZetaChains :=
  supply (3/2) (GChi PChar.one) (by norm_num) hosts (hypV_of_cls _ _)

theorem tiedOfChains (chains : ZetaChains) : ZetaTiedWindows := by
  obtain ⟨d, l, ε₀, pos, good⟩ := chains
  refine ⟨d, l, ε₀, pos, fun ε hε hsmall => ?_⟩
  obtain ⟨F, inClass, estimates⟩ := good ε hε hsmall
  exact ⟨F, eFamC_of_cls _ _ F inClass, inClass.1, estimates⟩

end RH17
