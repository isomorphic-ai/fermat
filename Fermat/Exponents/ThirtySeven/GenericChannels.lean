import Fermat.Descent.GenericIrregular.ChannelCertificate
import Fermat.Exponents.ThirtySeven.ArithmeticCertificate

/-!
# Axis-8 channel certificate at exponent 37

The complete low-index scan has one irregular channel, `j = 32`.  Its
Faulhaber power sum at index `32 * 37 = 1184` has correction weight `2`
modulo `37`.  The resulting one-by-one weighted moment is therefore
nondegenerate.
-/

namespace Fermat.ThirtySeven.GenericChannels

open Fermat.GenericIrregular.ChannelCertificate
open Fermat.Irregular

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- The sole lifted irregular channel at exponent `37`. -/
def channelThirtyTwo : LiftedPowerSumCertificate 37 where
  index := 32
  chooseQuotient := 7476560
  correction := 2
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
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 37)
    · decide
    · norm_num
  choose_eq := by
    rw [show 32 * 37 + 1 = 1185 by norm_num,
      show 32 * 37 - 2 = 1182 by norm_num,
      ← Nat.choose_symm (by norm_num : 1182 ≤ 1185)]
    norm_num [Nat.choose]
  powerSum := by
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    decide
  target_denominator := by
    apply BernoulliData.bernoulli_denominatorPrimeTo (p := 37)
    · decide
    · norm_num

/-- The unique channel, indexed as a one-element finite family. -/
def channelFamily : Fin 1 → LiftedPowerSumCertificate 37 :=
  fun _ ↦ channelThirtyTwo

/-- One nonzero weighted moment compresses the complete exponent-37 scan. -/
def fixedChannelCertificate : FixedChannelCertificate 37 1 where
  channel := channelFamily
  index_injective := fun _ _ _ ↦ Subsingleton.elim _ _
  complete := by
    intro j hj hirregular
    have hj' : 2 ≤ j ∧ j ≤ 34 ∧ Even j := by
      simpa [VandiverData.indices, and_assoc] using hj
    have hmem :
        j ∈ Fermat.ThirtySeven.ArithmeticCertificate.irregularIndices 37 := by
      simp only [
        Fermat.ThirtySeven.ArithmeticCertificate.irregularIndices,
        Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hj'.1, hj'.2.1⟩, hj'.2.2, hirregular⟩
    rw [
      Fermat.ThirtySeven.ArithmeticCertificate.irregularIndices_thirtySeven
    ] at hmem
    have hj32 : j = 32 := by
      simpa using hmem
    refine ⟨0, ?_⟩
    simp [hj32, channelFamily, channelThirtyTwo]
  moment_nondegenerate := by
    decide

/-- Regression endpoint: the generic axis-8 engine recovers every
Bernoulli cube condition needed at exponent `37`. -/
theorem bernoulliCubeCondition_thirtySeven :
    Fermat.Irregular.VandiverData.BernoulliCubeCondition 37 :=
  fixedChannelCertificate.bernoulliCubeCondition (by norm_num)

end Fermat.ThirtySeven.GenericChannels
