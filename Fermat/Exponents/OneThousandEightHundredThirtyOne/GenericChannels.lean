import Fermat.Descent.GenericIrregular.ChannelCertificate
import Fermat.Exponents.OneThousandEightHundredThirtyOne.IrregularScan
import Fermat.Exponents.OneThousandEightHundredThirtyOne.PowerSumCertificates

/-!
# One-channel Case-II.2 certificate at exponent 1831

The complete low-index scan has the single possible irregular channel
`1274`.  Its lifted Faulhaber correction is `1484` modulo `1831`; the
one-by-one weighted moment certifies its nonvanishing through the same
arbitrary-channel interface used by the smaller ladder rungs.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.GenericChannels

open Fermat.GenericIrregular.ChannelCertificate
open Fermat.Irregular
open Fermat.OneThousandEightHundredThirtyOne.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

/-- The lifted channel attached to the irregular index `1274`. -/
def channelOneThousandTwoHundredSeventyFour :
    LiftedPowerSumCertificate 1831 where
  index := 1274
  chooseQuotient := 1155403615531165
  correction := 1484
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
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 1831)
    · decide
    · norm_num
  choose_eq := by
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    rw [← Nat.choose_symm (by norm_num : 2332692 ≤ 2332695)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  powerSum := by
    norm_num only [Nat.reduceMul, Nat.cast_ofNat, Nat.reducePow]
    rw [powerSum_2332694]
    norm_num
  target_denominator := by
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 1831)
    · decide
    · norm_num

/-- The sole possible irregular channel as a finite family. -/
def channelFamily : Fin 1 → LiftedPowerSumCertificate 1831 :=
  fun _ ↦ channelOneThousandTwoHundredSeventyFour

/-- The one-dimensional weighted-moment certificate at exponent `1831`. -/
def fixedChannelCertificate : FixedChannelCertificate 1831 1 where
  channel := channelFamily
  index_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  complete := by
    intro j hj hirregular
    have hj1274 : j = 1274 :=
      Fermat.OneThousandEightHundredThirtyOne.IrregularScan.completeIrregularScan
        j hj hirregular
    refine ⟨0, ?_⟩
    simp [hj1274, channelFamily, channelOneThousandTwoHundredSeventyFour]
  moment_nondegenerate := by
    decide

/-- Regression: the generic axis-8 engine recovers the Bernoulli cube
condition required at exponent `1831`. -/
theorem bernoulliCubeCondition_oneThousandEightHundredThirtyOne_generic :
    Fermat.Irregular.VandiverData.BernoulliCubeCondition 1831 :=
  fixedChannelCertificate.bernoulliCubeCondition (by norm_num)

end Fermat.OneThousandEightHundredThirtyOne.GenericChannels
