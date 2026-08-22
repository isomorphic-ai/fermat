import Fermat.Descent.GenericIrregular.ChannelCertificate
import Fermat.Exponents.SixHundredNinetyOne.IrregularScan
import Fermat.Exponents.SixHundredNinetyOne.PowerSumCertificates

/-!
# Axis-8 channel certificate at exponent 691

The complete low-index scan has two possible irregular channels, `12` and
`200`.  Their lifted Faulhaber corrections are respectively `288` and `429`
modulo `691`.  One nonzero two-by-two weighted-moment determinant certifies
both channels simultaneously.
-/

namespace Fermat.SixHundredNinetyOne.GenericChannels

open Fermat.GenericIrregular.ChannelCertificate
open Fermat.Irregular
open Fermat.SixHundredNinetyOne.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

/-- The lifted channel attached to the irregular index `12`. -/
def channelTwelve : LiftedPowerSumCertificate 691 where
  index := 12
  chooseQuotient := 137514526
  correction := 288
  index_mem := by
    norm_num [VandiverData.indices]
  target_ge_six := by
    norm_num
  target_even := by
    norm_num
  denominator_next := by
    norm_num
  previous_integral := by
    apply DirectBernoulli.pIntegral_of_denominatorPrimeTo
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 691)
    · decide
    · norm_num
  choose_eq := by
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    rw [← Nat.choose_symm (by norm_num : 8290 ≤ 8293)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  powerSum := by
    norm_num only [Nat.reduceMul, Nat.cast_ofNat, Nat.reducePow]
    exact powerSum_8292
  target_denominator := by
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 691)
    · decide
    · norm_num

/-- The lifted channel attached to the irregular index `200`. -/
def channelTwoHundred : LiftedPowerSumCertificate 691 where
  index := 200
  chooseQuotient := 636641333300
  correction := 429
  index_mem := by
    norm_num [VandiverData.indices]
  target_ge_six := by
    norm_num
  target_even := by
    norm_num
  denominator_next := by
    norm_num
  previous_integral := by
    apply DirectBernoulli.pIntegral_of_denominatorPrimeTo
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 691)
    · decide
    · norm_num
  choose_eq := by
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    rw [← Nat.choose_symm (by norm_num : 138198 ≤ 138201)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  powerSum := by
    norm_num only [Nat.reduceMul, Nat.cast_ofNat, Nat.reducePow]
    exact powerSum_138200
  target_denominator := by
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 691)
    · decide
    · norm_num

/-- The two candidate irregular channels in increasing order. -/
def channelFamily : Fin 2 → LiftedPowerSumCertificate 691 :=
  ![channelTwelve, channelTwoHundred]

/-- The complete two-channel axis-8 certificate at exponent `691`. -/
def fixedChannelCertificate : FixedChannelCertificate 691 2 where
  channel := channelFamily
  index_injective := by
    decide
  complete := by
    intro j hj hirregular
    rcases
        Fermat.SixHundredNinetyOne.IrregularScan.completeIrregularScan
          j hj hirregular with hj12 | hj200
    · refine ⟨0, ?_⟩
      simp [hj12, channelFamily, channelTwelve]
    · refine ⟨1, ?_⟩
      simp [hj200, channelFamily, channelTwoHundred]
  moment_nondegenerate := by
    decide

/-- Regression endpoint: the axis-8 engine recovers every Bernoulli cube
condition required at exponent `691`. -/
theorem bernoulliCubeCondition_sixHundredNinetyOne_generic :
    Fermat.Irregular.VandiverData.BernoulliCubeCondition 691 :=
  fixedChannelCertificate.bernoulliCubeCondition (by norm_num)

end Fermat.SixHundredNinetyOne.GenericChannels
