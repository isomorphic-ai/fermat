import Fermat.Certificates.CaseII_1.BernoulliChannelCertificate157
import Fermat.Descent.GenericIrregular.BernoulliChannelLadder
import Fermat.Exponents.OneHundredFiftySeven.FirstCase
import Fermat.Exponents.OneHundredFiftySeven.GenericChannels
import Fermat.Exponents.OneHundredFiftySeven.GenericLemmaTwoChannels

/-!
# Full two-channel ladder at exponent 157

This is a new end-to-end route parallel to the historical exponent proof.
The same ordered support `{62, 110}` indexes the normalized Case-II.1
projection receipt and the lifted Case-II.2 power-sum channels.  The final
assembly uses the q-free finite-index proof for the same historical
Lemma-II unit system and the explicit Sophie--Germain certificate.
-/

open scoped NumberField

namespace Fermat.OneHundredFiftySeven.BernoulliChannelLadder

noncomputable section

open Fermat.GenericIrregular.BernoulliChannelLadder

local instance : Fact (Nat.Prime 157) :=
  ⟨Fermat.OneHundredFiftySeven.prime_157⟩

local instance : NeZero (157 : ℚ) := ⟨by norm_num⟩

local instance :
    IsCyclotomicExtension {157} ℚ (CyclotomicField 157 ℚ) :=
  CyclotomicField.isCyclotomicExtension 157 ℚ

local instance :
    NumberField.IsCMField (CyclotomicField 157 ℚ) :=
  IsCyclotomicExtension.IsCMField (p := 157)
    (CyclotomicField 157 ℚ) (by norm_num)

/-- The existing explicit Sophie--Germain witness, packaged locally so the
new ladder does not import the historical full second-case assembly. -/
def sophieGermainCertificate :
    Fermat.GenericIrregular.FixedExponent.SophieGermainCertificate 157 where
  auxiliaryPrime := 1571
  auxiliaryPrime_isPrime :=
    Fermat.OneHundredFiftySeven.prime_1571
  noConsecutivePowers :=
    Fermat.OneHundredFiftySeven.noConsecutivePowers_157_1571
  exponentNotPower :=
    Fermat.OneHundredFiftySeven.exponentNotPower_157_1571

/-- The two-channel full-ladder certificate at exponent `157`.  Its finite
index check states that both descent axes use literally the same ordered
Bernoulli support. -/
def certificate : LadderCertificate 157 2 where
  exponent_atLeastFive := by norm_num
  support :=
    Fermat.Certificates.CaseII_1.BernoulliChannelCertificate157.support
  channels :=
    Fermat.OneHundredFiftySeven.GenericChannels.fixedChannelCertificate
  projectionKernel :=
    Fermat.Certificates.CaseII_1.BernoulliChannelCertificate157.projectionKernelCertificate
  channel_index_eq := by
    intro i
    fin_cases i <;> rfl
  unitSystem :=
    Fermat.OneHundredFiftySeven.GenericLemmaTwoChannels.lemmaTwoUnitSystem157Channels
  sophieGermain := sophieGermainCertificate

/-- Fermat's Last Theorem at exponent `157`, through the new two-channel
ladder and without modifying the historical endpoint route. -/
theorem holdsAt_oneHundredFiftySeven_ladder : Fermat.HoldsAt 157 :=
  holdsAt_of_ladderCertificate certificate

end


end Fermat.OneHundredFiftySeven.BernoulliChannelLadder
