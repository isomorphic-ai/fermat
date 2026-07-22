import Fermat.Cases
import Fermat.FiftyNine.FirstCase

/-!
# The explicit second-case boundary at exponent 59

The uploaded package supplies a one-component Kummer certificate: its
finite data identify the sole irregular index `44`, certify the relevant
Bernoulli valuations, and give a nonsingular circular-unit residue matrix.
The global implication turning those data into the exclusion of a primitive
second-case solution is not yet a theorem of Mathlib or this repository.

This file therefore names that remaining proposition exactly and proves the
final assembly from it.  It introduces no axiom and does not claim that the
finite package alone has already discharged the boundary.
-/

namespace Fermat.FiftyNine

/-- The sole remaining endpoint needed after the checked Sophie--Germain
first case.  Mathematically this is the exponent-`59` specialization of
Kummer's one-component primary-singular-number theorem, including the
odd-primary circular-unit-index bridge used to establish its hypotheses. -/
def OneComponentSecondCaseBridge : Prop :=
  Fermat.SecondCaseExcluded 59

/-- The generic first/second-case assembly specialized to the exact
auxiliary prime `827`. -/
theorem holdsAt_fiftyNine_of_oneComponentSecondCaseBridge
    (hsecond : OneComponentSecondCaseBridge) : Fermat.HoldsAt 59 := by
  exact Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    prime_59 (by norm_num) prime_827
    noConsecutivePowers_59_827 exponentNotPower_59_827 hsecond

end Fermat.FiftyNine
