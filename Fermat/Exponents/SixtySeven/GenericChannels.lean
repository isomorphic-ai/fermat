import Fermat.Descent.GenericIrregular.ChannelCertificate
import Fermat.Exponents.SixtySeven.ArithmeticCertificate
import Fermat.Exponents.SixtySeven.HighBernoulli

/-!
# Axis-8 channel certificate at exponent 67

The complete low-index scan has one irregular channel, `j = 58`.  Its
Faulhaber power sum at index `58 * 67 = 3886` has correction weight `41`
modulo `67`.  The resulting one-by-one weighted moment is therefore
nondegenerate.
-/

namespace Fermat.SixtySeven.GenericChannels

open Fermat.GenericIrregular.ChannelCertificate
open Fermat.Irregular

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 67) :=
  ⟨Fermat.SixtySeven.prime_67⟩

/-- The sole lifted irregular channel at exponent `67`. -/
def channelFiftyEight : LiftedPowerSumCertificate 67 where
  index := 58
  chooseQuotient := 145976285
  correction := 41
  index_mem := by
    norm_num [VandiverData.indices]
  target_ge_six := by
    norm_num
  target_even := by
    norm_num
  denominator_next := by
    norm_num
  previous_integral :=
    Fermat.SixtySeven.HighBernoulli.previousBernoulli_pIntegral
  choose_eq := by
    simpa using Fermat.SixtySeven.HighBernoulli.choose_3887_3884
  powerSum := by
    rw [
      show 58 * 67 = 3886 by norm_num,
      Fermat.SixtySeven.HighBernoulli.powerSum_mod_sixtySeven_pow_four
    ]
    norm_num
  target_denominator :=
    Fermat.SixtySeven.HighBernoulli.targetBernoulli_denominatorPrimeTo

/-- The unique channel, indexed as a one-element finite family. -/
def channelFamily : Fin 1 → LiftedPowerSumCertificate 67 :=
  fun _ ↦ channelFiftyEight

/-- One nonzero weighted moment compresses the complete exponent-67 scan. -/
def fixedChannelCertificate : FixedChannelCertificate 67 1 where
  channel := channelFamily
  index_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  complete := by
    intro j hj hirregular
    have hj' : 2 ≤ j ∧ j ≤ 64 ∧ Even j := by
      simpa [VandiverData.indices, and_assoc] using hj
    have hmem :
        j ∈ Fermat.SixtySeven.ArithmeticCertificate.irregularIndices 67 := by
      simp only [
        Fermat.SixtySeven.ArithmeticCertificate.irregularIndices,
        Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hj'.1, hj'.2.1⟩, hj'.2.2, hirregular⟩
    rw [
      Fermat.SixtySeven.ArithmeticCertificate.irregularIndices_sixtySeven
    ] at hmem
    have hj58 : j = 58 := by
      simpa using hmem
    refine ⟨0, ?_⟩
    simp [hj58, channelFamily, channelFiftyEight]
  moment_nondegenerate := by
    decide

/-- Regression endpoint: the generic axis-8 engine recovers every
Bernoulli cube condition needed at exponent `67`. -/
theorem bernoulliCubeCondition_sixtySeven_generic :
    Fermat.Irregular.VandiverData.BernoulliCubeCondition 67 :=
  fixedChannelCertificate.bernoulliCubeCondition (by norm_num)

end Fermat.SixtySeven.GenericChannels
