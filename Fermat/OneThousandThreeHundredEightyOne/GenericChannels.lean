import Fermat.GenericIrregular.ChannelCertificate
import Fermat.OneThousandThreeHundredEightyOne.IrregularScan
import Fermat.OneThousandThreeHundredEightyOne.PowerSumCertificates

/-!
# Axis-8 channel certificate at exponent 1381

The complete compact scan has the single irregular channel `266`.  Its
lifted Faulhaber correction weight is `561` modulo `1381`.  The resulting
one-by-one weighted-moment determinant certifies its nonvanishing.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.GenericChannels

open Fermat.GenericIrregular.ChannelCertificate
open Fermat.Irregular
open Fermat.OneThousandThreeHundredEightyOne.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

/-- The lifted channel attached to the irregular index `266`. -/
def channelTwoHundredSixtySix : LiftedPowerSumCertificate 1381 where
  index := 266
  chooseQuotient := 5982476711365
  correction := 561
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
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 1381)
    · decide
    · norm_num
  choose_eq := by
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    rw [← Nat.choose_symm (by norm_num : 367344 ≤ 367347)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  powerSum := by
    norm_num only [Nat.reduceMul, Nat.cast_ofNat, Nat.reducePow]
    rw [powerSum_367346]
    norm_num
  target_denominator := by
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 1381)
    · decide
    · norm_num

/-- The unique channel, indexed as a one-element finite family. -/
def channelFamily : Fin 1 → LiftedPowerSumCertificate 1381 :=
  fun _ ↦ channelTwoHundredSixtySix

/-- One nonzero weighted moment compresses the complete exponent-1381
scan. -/
def fixedChannelCertificate : FixedChannelCertificate 1381 1 where
  channel := channelFamily
  index_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  complete := by
    intro j hj hirregular
    have hj266 :
        j = 266 :=
      Fermat.OneThousandThreeHundredEightyOne.IrregularScan.completeIrregularScan
        j hj hirregular
    refine ⟨0, ?_⟩
    simp [hj266, channelFamily, channelTwoHundredSixtySix]
  moment_nondegenerate := by
    decide

/-- Regression endpoint: the generic axis-8 engine recovers every
Bernoulli cube condition needed at exponent `1381`. -/
theorem bernoulliCubeCondition_oneThousandThreeHundredEightyOne_generic :
    Fermat.Irregular.VandiverData.BernoulliCubeCondition 1381 :=
  fixedChannelCertificate.bernoulliCubeCondition (by norm_num)

end Fermat.OneThousandThreeHundredEightyOne.GenericChannels
