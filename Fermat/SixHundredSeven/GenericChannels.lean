import Fermat.GenericIrregular.ChannelCertificate
import Fermat.SixHundredSeven.IrregularScan
import Fermat.SixHundredSeven.PowerSumCertificates

/-!
# Axis-8 channel certificate at exponent 607

The complete compact scan has the sole irregular channel `592`.  Its lifted
Faulhaber correction weight is `511` modulo `607`.  The resulting one-by-one
weighted moment is nondegenerate, certifying the channel without storing its
Bernoulli conclusion.
-/

namespace Fermat.SixHundredSeven.GenericChannels

open Fermat.GenericIrregular.ChannelCertificate
open Fermat.Irregular
open Fermat.SixHundredSeven.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 607) :=
  ⟨by norm_num⟩

/-- The lifted channel attached to the irregular index `592`. -/
def channelFiveHundredNinetyTwo : LiftedPowerSumCertificate 607 where
  index := 592
  chooseQuotient := 12740640219720
  correction := 511
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
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 607)
    · decide
    · norm_num
  choose_eq := by
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    rw [← Nat.choose_symm (by norm_num : 359342 ≤ 359345)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  powerSum := by
    norm_num only [Nat.reduceMul, Nat.cast_ofNat, Nat.reducePow]
    exact powerSum_359344
  target_denominator := by
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 607)
    · decide
    · norm_num

/-- The unique channel, indexed as a one-element finite family. -/
def channelFamily : Fin 1 → LiftedPowerSumCertificate 607 :=
  fun _ ↦ channelFiveHundredNinetyTwo

/-- One nonzero weighted moment compresses the complete exponent-607 scan. -/
def fixedChannelCertificate : FixedChannelCertificate 607 1 where
  channel := channelFamily
  index_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  complete := by
    intro j hj hirregular
    have hj592 :
        j = 592 :=
      Fermat.SixHundredSeven.IrregularScan.completeIrregularScan
        j hj hirregular
    refine ⟨0, ?_⟩
    simp [hj592, channelFamily, channelFiveHundredNinetyTwo]
  moment_nondegenerate := by
    decide

/-- Regression endpoint: the generic axis-8 engine recovers every
Bernoulli cube condition needed at exponent `607`. -/
theorem bernoulliCubeCondition_sixHundredSeven_generic :
    Fermat.Irregular.VandiverData.BernoulliCubeCondition 607 :=
  fixedChannelCertificate.bernoulliCubeCondition (by norm_num)

end Fermat.SixHundredSeven.GenericChannels
