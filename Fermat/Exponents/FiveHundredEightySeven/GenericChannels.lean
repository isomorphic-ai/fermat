import Fermat.Descent.GenericIrregular.ChannelCertificate
import Fermat.Exponents.FiveHundredEightySeven.IrregularScan
import Fermat.Exponents.FiveHundredEightySeven.PowerSumCertificates

/-!
# Axis-8 channel certificate at exponent 587

The complete compact scan has the two irregular channels `90` and `92`.
Their lifted Faulhaber correction weights are respectively `498` and `242`
modulo `587`.  A single two-by-two weighted-moment determinant certifies
both nonvanishing statements simultaneously.
-/

namespace Fermat.FiveHundredEightySeven.GenericChannels

open Fermat.GenericIrregular.ChannelCertificate
open Fermat.Irregular
open Fermat.FiveHundredEightySeven.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 587) :=
  ⟨by norm_num⟩

/-- The lifted channel attached to the irregular index `90`. -/
def channelNinety : LiftedPowerSumCertificate 587 where
  index := 90
  chooseQuotient := 41865133485
  correction := 498
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
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 587)
    · decide
    · norm_num
  choose_eq := by
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    rw [← Nat.choose_symm (by norm_num : 52828 ≤ 52831)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  powerSum := by
    norm_num only [Nat.reduceMul, Nat.cast_ofNat, Nat.reducePow]
    rw [powerSum_52830]
    norm_num
  target_denominator := by
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 587)
    · decide
    · norm_num

/-- The lifted channel attached to the irregular index `92`. -/
def channelNinetyTwo : LiftedPowerSumCertificate 587 where
  index := 92
  chooseQuotient := 44718624230
  correction := 242
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
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 587)
    · decide
    · norm_num
  choose_eq := by
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    rw [← Nat.choose_symm (by norm_num : 54002 ≤ 54005)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  powerSum := by
    norm_num only [Nat.reduceMul, Nat.cast_ofNat, Nat.reducePow]
    rw [powerSum_54004]
    norm_num
  target_denominator := by
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 587)
    · decide
    · norm_num

/-- The two genuine irregular channels in increasing order. -/
def channelFamily : Fin 2 → LiftedPowerSumCertificate 587 :=
  ![channelNinety, channelNinetyTwo]

/-- One two-dimensional weighted moment compresses the complete scan. -/
def fixedChannelCertificate : FixedChannelCertificate 587 2 where
  channel := channelFamily
  index_injective := by
    decide
  complete := by
    intro j hj hirregular
    rcases
        Fermat.FiveHundredEightySeven.IrregularScan.completeIrregularScan
          j hj hirregular with hj90 | hj92
    · refine ⟨0, ?_⟩
      simp [hj90, channelFamily, channelNinety]
    · refine ⟨1, ?_⟩
      simp [hj92, channelFamily, channelNinetyTwo]
  moment_nondegenerate := by
    decide

/-- Regression endpoint: the generic axis-8 engine recovers every
Bernoulli cube condition needed at exponent `587`. -/
theorem bernoulliCubeCondition_fiveHundredEightySeven_generic :
    Fermat.Irregular.VandiverData.BernoulliCubeCondition 587 :=
  fixedChannelCertificate.bernoulliCubeCondition (by norm_num)

end Fermat.FiveHundredEightySeven.GenericChannels
