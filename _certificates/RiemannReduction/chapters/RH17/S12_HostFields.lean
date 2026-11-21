import Development.AutomorphicArithmetic.CharacterBoxes.SupplyChi

/-! # 12. Supply auxiliary fields at the scales that matter
The source packages a cohomology estimate into `VWinAt`. It controls losses
from divisibility over a long interval. Specialize the archive's host-field
construction to the character modulo one. For this deduction, that single
instance of the cohomology estimate suffices. The integer 401 is the source's
cutoff for twists in the cohomology estimate. -/

namespace RH17

open Formalism.HC UpperTheory.Top GlobalTheory.EX

abbrev ZetaCohomology := VWinAt PChar.one 401

abbrev ZetaHosts := HostExW (3/2) (GChi PChar.one).req

theorem hostsOfCohomology (h : ZetaCohomology) : ZetaHosts := supplyChi PChar.one h

end RH17
