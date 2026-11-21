import RH17.S15_ArithmeticWindows

/-! # 16. Join the two arithmetic inputs
The host construction and the chain construction enter at different points.
Together they give one-sided windows for G at every exponent above 1/2 and
below 1. The analytic criterion in file 9 needs exactly these windows. -/

namespace RH17

open UpperTheory.Top

theorem primeWindowsOfChains (h : ZetaChains) : NearHalf primeError (1/2) :=
  primeWindowsOfTied (tiedOfChains h)

theorem primeWindowsOfArithmetic (chains : TopG) (cohomology : ZetaCohomology) :
    NearHalf primeError (1/2) :=
  primeWindowsOfChains (chainsOfHosts chains (hostsOfCohomology cohomology))

end RH17
