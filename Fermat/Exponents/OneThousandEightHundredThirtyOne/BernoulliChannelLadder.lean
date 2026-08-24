import Fermat.Certificates.CaseII_1.BernoulliChannelCertificate1831
import Fermat.Descent.GenericIrregular.BernoulliChannelLadder
import Fermat.Exponents.OneThousandEightHundredThirtyOne.FirstCase
import Fermat.Exponents.OneThousandEightHundredThirtyOne.GenericChannels
import Fermat.Exponents.OneThousandEightHundredThirtyOne.GenericLemmaTwo

/-!
# Full one-channel ladder at exponent 1831

This is a new end-to-end route parallel to the historical exponent proof.
The same index `1274` names both the normalized Case-II.1 projection receipt
and the lifted Case-II.2 power-sum channel.  The final assembly also consumes
the existing finite Lemma-II unit system and explicit Sophie--Germain data.
-/

open scoped NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.BernoulliChannelLadder

noncomputable section

open Fermat.GenericIrregular.BernoulliChannelLadder

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩

local instance : NeZero (1831 : ℚ) := ⟨by norm_num⟩

local instance :
    IsCyclotomicExtension {1831} ℚ (CyclotomicField 1831 ℚ) :=
  CyclotomicField.isCyclotomicExtension 1831 ℚ

local instance :
    NumberField.IsCMField (CyclotomicField 1831 ℚ) :=
  IsCyclotomicExtension.IsCMField (p := 1831)
    (CyclotomicField 1831 ℚ) (by norm_num)

/-- The historical finite Sophie--Germain witness, retained as explicit
Case-I data in the new ladder. -/
def sophieGermainCertificate :
    Fermat.GenericIrregular.FixedExponent.SophieGermainCertificate 1831 where
  auxiliaryPrime := 358877
  auxiliaryPrime_isPrime :=
    Fermat.OneThousandEightHundredThirtyOne.prime_358877
  noConsecutivePowers :=
    Fermat.OneThousandEightHundredThirtyOne.noConsecutivePowers_1831_358877
  exponentNotPower :=
    Fermat.OneThousandEightHundredThirtyOne.exponentNotPower_1831_358877

/-- The first rung of the full arbitrary-channel ladder.  The index-agreement
field is a one-entry finite check, not an assumed character correspondence. -/
def certificate : LadderCertificate 1831 1 where
  exponent_atLeastFive := by norm_num
  support :=
    Fermat.Certificates.CaseII_1.BernoulliChannelCertificate1831.support
  channels :=
    Fermat.OneThousandEightHundredThirtyOne.GenericChannels.fixedChannelCertificate
  projectionKernel :=
    Fermat.Certificates.CaseII_1.BernoulliChannelCertificate1831.projectionKernelCertificate
  channel_index_eq := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  unitSystem :=
    Fermat.OneThousandEightHundredThirtyOne.GenericLemmaTwo.lemmaTwoUnitSystem1831
  sophieGermain := sophieGermainCertificate

/-- Fermat's Last Theorem at exponent `1831`, through the new one-channel
ladder and without modifying the historical exponent route. -/
theorem holdsAt_oneThousandEightHundredThirtyOne_ladder :
    Fermat.HoldsAt 1831 :=
  holdsAt_of_ladderCertificate certificate

end

end Fermat.OneThousandEightHundredThirtyOne.BernoulliChannelLadder
