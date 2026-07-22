import Fermat.Cases
import Fermat.Irregular.VandiverData
import Fermat.OneHundredFiftySeven.FirstCase

/-!
# The explicit second-case boundary at exponent 157

The uploaded package supplies two finite Bernoulli correction channels
(`62` and `110`) and a nonsingular second circular-unit probe.  The generic
theorems that turn those certificates into the historical
primary-singular-number descent are intentionally not assumed as axioms.

This file names the exact remaining endpoint and proves the otherwise
complete first/second-case assembly.
-/

namespace Fermat.OneHundredFiftySeven

/-- The sole remaining logical endpoint after the checked finite data.  It
is exactly the exponent-157 specialization of the historical finite-channel
second-case theorem, including the circular-unit/class-number bridge. -/
def TwoComponentSecondCaseBridge : Prop :=
  Fermat.SecondCaseExcluded 157

/-- The finite Bernoulli proposition consumed by the historical bridge.
Its two exceptional modular power sums are checked in `FoldCertificates`;
the shared Faulhaber endpoint deriving this proposition is being extracted
from the exponent-37 development. -/
abbrev BernoulliCubeCondition : Prop :=
  Fermat.Irregular.VandiverData.BernoulliCubeCondition 157

/-- The generic first/second-case assembly specialized to auxiliary prime
1571. -/
theorem holdsAt_oneHundredFiftySeven_of_twoComponentSecondCaseBridge
    (hsecond : TwoComponentSecondCaseBridge) : Fermat.HoldsAt 157 := by
  exact Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    prime_157 (by norm_num) prime_1571
    noConsecutivePowers_157_1571 exponentNotPower_157_1571 hsecond

end Fermat.OneHundredFiftySeven
