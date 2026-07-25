import Fermat.GenericIrregular.ChannelCertificate
import Fermat.FiftyNine.ArithmeticCertificate

/-!
# Axis-8 channel certificate at exponent 59

The complete low-index scan has one irregular channel, `j = 44`.  Its
Faulhaber power sum at index `44 * 59 = 2596` has correction weight `18`
modulo `59`, since `62658 = 59^2 * 18`.  The resulting one-by-one weighted
moment is therefore nondegenerate.
-/

namespace Fermat.FiftyNine.GenericChannels

open Fermat.GenericIrregular.ChannelCertificate
open Fermat.Irregular

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

/-- The sole lifted irregular channel at exponent `59`. -/
def channelFortyFour : LiftedPowerSumCertificate 59 where
  index := 44
  chooseQuotient := 49420910
  correction := 18
  index_mem := by
    norm_num [VandiverData.indices]
  target_ge_six := by
    norm_num
  target_even := by
    norm_num
  denominator_next := by
    norm_num
  previous_integral :=
    Fermat.FiftyNine.HighBernoulli.pIntegral_bernoulli_2594
  choose_eq := by
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
    exact Fermat.FiftyNine.HighBernoulli.choose_2597_2594
  powerSum := by
    norm_num only [Nat.reduceMul, Nat.cast_ofNat, Nat.reducePow]
    exact Fermat.FiftyNine.HighBernoulli.powerSum_mod_fiftyNine_pow_four
  target_denominator :=
    Fermat.FiftyNine.HighBernoulli.denominatorPrimeTo_bernoulli_2596

/-- The unique channel, indexed as a one-element finite family. -/
def channelFamily : Fin 1 → LiftedPowerSumCertificate 59 :=
  fun _ ↦ channelFortyFour

/-- One nonzero weighted moment compresses the complete exponent-59 scan. -/
def fixedChannelCertificate : FixedChannelCertificate 59 1 where
  channel := channelFamily
  index_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  complete := by
    intro j hj hirregular
    have hj' : 2 ≤ j ∧ j ≤ 56 ∧ Even j := by
      simpa [VandiverData.indices, and_assoc] using hj
    have hmem :
        j ∈ Fermat.FiftyNine.ArithmeticCertificate.irregularIndices 59 := by
      simp only [
        Fermat.FiftyNine.ArithmeticCertificate.irregularIndices,
        Fermat.ThirtySeven.ArithmeticCertificate.irregularIndices,
        Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hj'.1, hj'.2.1⟩, hj'.2.2, hirregular⟩
    rw [
      Fermat.FiftyNine.ArithmeticCertificate.irregularIndices_fiftyNine
    ] at hmem
    have hj44 : j = 44 := by
      simpa using hmem
    refine ⟨0, ?_⟩
    simp [hj44, channelFamily, channelFortyFour]
  moment_nondegenerate := by
    decide

/-- Regression endpoint: the generic axis-8 engine recovers every
Bernoulli cube condition needed at exponent `59`. -/
theorem bernoulliCubeCondition_fiftyNine_generic :
    Fermat.Irregular.VandiverData.BernoulliCubeCondition 59 :=
  fixedChannelCertificate.bernoulliCubeCondition (by norm_num)

end Fermat.FiftyNine.GenericChannels
