import Fermat.GenericIrregular.ChannelCertificate
import Fermat.OneHundredFiftySeven.IrregularScan
import Fermat.OneHundredFiftySeven.PowerSumCertificates

/-!
# Axis-8 channel certificate at exponent 157

The complete low-index scan has two irregular channels, `62` and `110`.
Their lifted Faulhaber corrections are respectively `3` and `16` modulo
`157`.  Unlike the one-channel regressions at 37, 59, and 67, this file
exercises the actual two-dimensional structure-preserving compression: one
nonzero weighted-moment determinant certifies both channels simultaneously.
-/

namespace Fermat.OneHundredFiftySeven.GenericChannels

open Fermat.GenericIrregular.ChannelCertificate
open Fermat.Irregular
open Fermat.OneHundredFiftySeven.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

/-- The lifted channel attached to the irregular index `62`. -/
def channelSixtyTwo : LiftedPowerSumCertificate 157 where
  index := 62
  chooseQuotient := 979091135
  correction := 3
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
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 157)
    · decide
    · norm_num
  choose_eq := by
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    rw [← Nat.choose_symm (by norm_num : 9732 ≤ 9735)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  powerSum := by
    norm_num only [Nat.reduceMul, Nat.cast_ofNat, Nat.reducePow]
    exact powerSum_9734
  target_denominator := by
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 157)
    · decide
    · norm_num

/-- The lifted channel attached to the irregular index `110`. -/
def channelOneHundredTen : LiftedPowerSumCertificate 157 where
  index := 110
  chooseQuotient := 5467969815
  correction := 16
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
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 157)
    · decide
    · norm_num
  choose_eq := by
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    rw [← Nat.choose_symm (by norm_num : 17268 ≤ 17271)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  powerSum := by
    norm_num only [Nat.reduceMul, Nat.cast_ofNat, Nat.reducePow]
    exact powerSum_17270
  target_denominator := by
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 157)
    · decide
    · norm_num

/-- The two genuine irregular channels in increasing order. -/
def channelFamily : Fin 2 → LiftedPowerSumCertificate 157 :=
  ![channelSixtyTwo, channelOneHundredTen]

/-- The first nontrivial axis-8 compression certificate: a two-by-two
weighted moment simultaneously certifies both correction channels. -/
def fixedChannelCertificate : FixedChannelCertificate 157 2 where
  channel := channelFamily
  index_injective := by
    decide
  complete := by
    intro j hj hirregular
    rcases
        Fermat.OneHundredFiftySeven.IrregularScan.completeIrregularScan
          j hj hirregular with hj62 | hj110
    · refine ⟨0, ?_⟩
      simp [hj62, channelFamily, channelSixtyTwo]
    · refine ⟨1, ?_⟩
      simp [hj110, channelFamily, channelOneHundredTen]
  moment_nondegenerate := by
    decide

/-- Regression endpoint: the two-dimensional axis-8 engine recovers every
Bernoulli cube condition needed at exponent `157`. -/
theorem bernoulliCubeCondition_oneHundredFiftySeven_generic :
    Fermat.Irregular.VandiverData.BernoulliCubeCondition 157 :=
  fixedChannelCertificate.bernoulliCubeCondition (by norm_num)

end Fermat.OneHundredFiftySeven.GenericChannels
