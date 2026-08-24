import Fermat.Certificates.CaseII_1.BernoulliChannelCertificate491
import Fermat.Descent.GenericIrregular.BernoulliChannelLadder
import Fermat.Exponents.FourHundredNinetyOne.FirstCase
import Fermat.Exponents.FourHundredNinetyOne.GenericChannels
import Fermat.Exponents.FourHundredNinetyOne.GenericLemmaTwoChannels

/-!
# Full three-channel ladder at exponent 491

This is a new end-to-end route parallel to the historical exponent proof.
The same ordered support `{292, 336, 338}` indexes the normalized Case-II.1
projection receipt and the lifted Case-II.2 power-sum channels. The final
assembly also consumes the existing finite Lemma-II unit system and explicit
Sophie--Germain data.
-/

open scoped NumberField

namespace Fermat.FourHundredNinetyOne.BernoulliChannelLadder

noncomputable section

open Fermat.GenericIrregular.BernoulliChannelLadder

local instance : Fact (Nat.Prime 491) :=
  ⟨Fermat.FourHundredNinetyOne.prime_491⟩

local instance : NeZero (491 : ℚ) := ⟨by norm_num⟩

local instance :
    IsCyclotomicExtension {491} ℚ (CyclotomicField 491 ℚ) :=
  CyclotomicField.isCyclotomicExtension 491 ℚ

local instance :
    NumberField.IsCMField (CyclotomicField 491 ℚ) :=
  IsCyclotomicExtension.IsCMField (p := 491)
    (CyclotomicField 491 ℚ) (by norm_num)

/-- The explicit finite Sophie--Germain witness at auxiliary prime `983`.
It is restated here so the new ladder does not import the historical full
second-case assembly merely to reuse this four-field bundle. -/
def sophieGermainCertificate :
    Fermat.GenericIrregular.FixedExponent.SophieGermainCertificate 491 where
  auxiliaryPrime := 983
  auxiliaryPrime_isPrime :=
    Fermat.FourHundredNinetyOne.prime_983
  noConsecutivePowers :=
    Fermat.FourHundredNinetyOne.noConsecutivePowers_491_983
  exponentNotPower :=
    Fermat.FourHundredNinetyOne.exponentNotPower_491_983

/-- The three-channel full-ladder certificate at exponent `491`. The finite
index-agreement field checks that both descent axes use literally the same
ordered Bernoulli support. -/
def certificate : LadderCertificate 491 3 where
  exponent_atLeastFive := by norm_num
  support :=
    Fermat.Certificates.CaseII_1.BernoulliChannelCertificate491.support
  channels :=
    Fermat.FourHundredNinetyOne.GenericChannels.fixedChannelCertificate
  projectionKernel :=
    Fermat.Certificates.CaseII_1.BernoulliChannelCertificate491.projectionKernelCertificate
  channel_index_eq := by
    intro i
    fin_cases i <;> rfl
  unitSystem :=
    Fermat.FourHundredNinetyOne.GenericLemmaTwoChannels.lemmaTwoUnitSystem491
  sophieGermain := sophieGermainCertificate

/-- Fermat's Last Theorem at exponent `491`, through the new three-channel
ladder and without modifying the historical endpoint route. -/
theorem holdsAt_fourHundredNinetyOne_ladder : Fermat.HoldsAt 491 :=
  holdsAt_of_ladderCertificate certificate

end

end Fermat.FourHundredNinetyOne.BernoulliChannelLadder
