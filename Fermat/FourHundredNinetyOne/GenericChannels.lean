import Fermat.GenericIrregular.ChannelCertificate
import Fermat.FourHundredNinetyOne.IrregularScan
import Fermat.FourHundredNinetyOne.PowerSumCertificates

/-!
# Axis-8 channel certificate at exponent 491

The complete low-index scan has three irregular channels, `292`, `336`,
and `338`.  Their lifted Faulhaber corrections are respectively `351`,
`412`, and `11` modulo `491`.  One nonzero three-by-three weighted-moment
determinant certifies all three channels simultaneously.
-/

namespace Fermat.FourHundredNinetyOne.GenericChannels

open Fermat.GenericIrregular.ChannelCertificate
open Fermat.Irregular
open Fermat.FourHundredNinetyOne.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

/-- The lifted channel attached to the irregular index `292`. -/
def channelTwoHundredNinetyTwo : LiftedPowerSumCertificate 491 where
  index := 292
  chooseQuotient := 1000369145306
  correction := 351
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
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 491)
    · decide
    · norm_num
  choose_eq := by
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    rw [← Nat.choose_symm (by norm_num : 143370 ≤ 143373)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  powerSum := by
    rw [show 292 * 491 = 143372 by norm_num, powerSum_143372]
    norm_num
  target_denominator := by
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 491)
    · decide
    · norm_num

/-- The lifted channel attached to the irregular index `336`. -/
def channelThreeHundredThirtySix : LiftedPowerSumCertificate 491 where
  index := 336
  chooseQuotient := 1524156512200
  correction := 412
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
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 491)
    · decide
    · norm_num
  choose_eq := by
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    rw [← Nat.choose_symm (by norm_num : 164974 ≤ 164977)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  powerSum := by
    rw [show 336 * 491 = 164976 by norm_num, powerSum_164976]
    norm_num
  target_denominator := by
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 491)
    · decide
    · norm_num

/-- The lifted channel attached to the irregular index `338`. -/
def channelThreeHundredThirtyEight : LiftedPowerSumCertificate 491 where
  index := 338
  chooseQuotient := 1551535920649
  correction := 11
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
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 491)
    · decide
    · norm_num
  choose_eq := by
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    rw [← Nat.choose_symm (by norm_num : 165956 ≤ 165959)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  powerSum := by
    rw [show 338 * 491 = 165958 by norm_num, powerSum_165958]
    norm_num
  target_denominator := by
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 491)
    · decide
    · norm_num

/-- The three genuine irregular channels in increasing order. -/
def channelFamily : Fin 3 → LiftedPowerSumCertificate 491 :=
  ![channelTwoHundredNinetyTwo, channelThreeHundredThirtySix,
    channelThreeHundredThirtyEight]

/-- A single three-dimensional weighted moment compresses all three
exponent-491 correction channels. -/
def fixedChannelCertificate : FixedChannelCertificate 491 3 where
  channel := channelFamily
  index_injective := by
    decide
  complete := by
    intro j hj hirregular
    rcases
        Fermat.FourHundredNinetyOne.IrregularScan.completeIrregularScan
          j hj hirregular with hj292 | hj336 | hj338
    · refine ⟨0, ?_⟩
      simp [hj292, channelFamily, channelTwoHundredNinetyTwo]
    · refine ⟨1, ?_⟩
      simp [hj336, channelFamily, channelThreeHundredThirtySix]
    · refine ⟨2, ?_⟩
      simp [hj338, channelFamily, channelThreeHundredThirtyEight]
  moment_nondegenerate := by
    decide

/-- Regression endpoint: the three-dimensional axis-8 engine recovers
every Bernoulli cube condition needed at exponent `491`. -/
theorem bernoulliCubeCondition_fourHundredNinetyOne_generic :
    Fermat.Irregular.VandiverData.BernoulliCubeCondition 491 :=
  fixedChannelCertificate.bernoulliCubeCondition (by norm_num)

end Fermat.FourHundredNinetyOne.GenericChannels
