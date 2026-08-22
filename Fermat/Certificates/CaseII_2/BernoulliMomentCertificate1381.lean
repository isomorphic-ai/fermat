import Fermat.Descent.GenericIrregular.WeightedMoment
import Fermat.Descent.Irregular.DirectBernoulli
import Fermat.Descent.Irregular.ModularBernoulliScan
import Fermat.Exponents.OneThousandThreeHundredEightyOne.IrregularScanCertificate

/-!
# Weighted Bernoulli moment certificate at exponent 1381

This module is the finite Case-II.2 receipt supplied by
`flt8-moment-1381.zip` (archive SHA-256
`02c8a98d90c444b72b0b3d9844ccb20af47196fead57ac75d3da102779f1679c`).

The low scan leaves `266` as the sole possible irregular channel.  Its
centered level is `0`, and its normalized lifted weight is `561` modulo
`1381`.  Thus the weighted moment matrix is the one-by-one matrix `[[561]]`.

The determinant proves nonvanishing of the supplied weight.  The separate
`liftedPowerSum_eq_weight1381` theorem is the necessary provenance bridge:
it kernel-checks that `561` is the residue attached to the actual lifted
Bernoulli index `266 * 1381 = 367346`.  Consequently this module does not
import the older exponent-local `PowerSumCertificates`, `HighBernoulli`,
`IrregularScan`, `GenericChannels`, or `VandiverData` assembly modules.
-/

open scoped BigOperators

namespace Fermat.Certificates.CaseII_2.BernoulliMomentCertificate1381

open Fermat.GenericIrregular.WeightedMoment
open Fermat.Irregular
open Fermat.Irregular.BernoulliData
open Fermat.Irregular.DirectBernoulli
open Fermat.Irregular.ModularBernoulliScan
open Fermat.Irregular.VandiverData
open Fermat.OneThousandThreeHundredEightyOne.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

/-- The single centered Bernoulli level in the archive. -/
def centeredLevel1381 : Fin 1 → ZMod 1381 := fun _ ↦ 0

/-- The normalized lifted Bernoulli weight recorded by the archive. -/
def liftedWeight1381 : Fin 1 → ZMod 1381 :=
  fun _ ↦ ((561 : ℕ) : ZMod 1381)

/-- A one-point level family is injective. -/
theorem centeredLevel1381_injective :
    Function.Injective centeredLevel1381 :=
  fun _ _ _ ↦ Subsingleton.elim _ _

/-- Exact value of the one-by-one weighted moment determinant. -/
theorem momentDet1381 :
    (weightedMoment centeredLevel1381 liftedWeight1381).det = 561 := by
  decide

/-- The weighted moment form at exponent `1381` is nondegenerate. -/
theorem momentNondegenerate1381 :
    (weightedMoment centeredLevel1381 liftedWeight1381).det ≠ 0 := by
  rw [momentDet1381]
  decide

/-- The moment determinant recovers nonvanishing of its unique weight. -/
theorem liftedWeight1381_ne_zero (i : Fin 1) :
    liftedWeight1381 i ≠ 0 :=
  weight_ne_zero_of_det_weightedMoment_ne_zero
    centeredLevel1381_injective momentNondegenerate1381 i

private theorem correction1381_ne_zero : (561 : ℕ) ≠ 0 := by
  intro hzero
  apply liftedWeight1381_ne_zero 0
  simp [liftedWeight1381, hzero]

private theorem residue1381_ne_zero : 1381 ^ 2 * 561 ≠ 0 :=
  mul_ne_zero (pow_ne_zero 2 (by norm_num)) correction1381_ne_zero

private theorem residue_not_dvd_cube_of_weight
    {p c : ℕ} [Fact p.Prime] (hweight : (c : ZMod p) ≠ 0) :
    ¬(p : ℤ) ^ 3 ∣ ((p ^ 2 * c : ℕ) : ℤ) := by
  intro hcube
  apply hweight
  have hp2 : (p : ℤ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Int.natCast_ne_zero.mpr
      (Fact.out : p.Prime).ne_zero)
  have hcancel :
      (p : ℤ) ^ 2 * p ∣ (p : ℤ) ^ 2 * c := by
    simpa only [pow_succ, Int.natCast_mul, Int.natCast_pow] using hcube
  have hdvd : (p : ℤ) ∣ (c : ℤ) :=
    (mul_dvd_mul_iff_left hp2).mp hcancel
  exact (ZMod.natCast_eq_zero_iff c p).2 (by exact_mod_cast hdvd)

private theorem residue1381_not_dvd_cube :
    ¬(1381 : ℤ) ^ 3 ∣ ((1381 ^ 2 * 561 : ℕ) : ℤ) :=
  residue_not_dvd_cube_of_weight <| by
    simpa only [liftedWeight1381] using
      liftedWeight1381_ne_zero (0 : Fin 1)

private theorem even_index_eq_scanIndex
    (k : ℕ) (hk2 : 2 ≤ k) (hk1378 : k ≤ 1378) (hkeven : Even k) :
    ∃ i : Fin 689, scanIndex i = k := by
  obtain ⟨r, hr⟩ := hkeven
  let i : Fin 689 := ⟨r - 1, by omega⟩
  refine ⟨i, ?_⟩
  simp only [scanIndex, i]
  omega

private theorem scanResidue_ne_zero_outside_channel
    (k : ℕ) (hk : k ∈ indices 1381)
    (hnot : k ∉ ({266} : Finset ℕ)) :
    scanResidue 1381 2 k ≠ 0 := by
  have hbounds : 2 ≤ k ∧ k ≤ 1378 ∧ Even k := by
    simpa [indices, and_assoc] using hk
  obtain ⟨i, hi⟩ :=
    even_index_eq_scanIndex k hbounds.1 hbounds.2.1 hbounds.2.2
  intro hzero
  have hchannel :=
    scanResidue_zero_only_at_channel i (hi ▸ hzero)
  rw [hi] at hchannel
  apply hnot
  simpa only [Finset.mem_singleton] using hchannel

/-- The kernel-checked low scan leaves only the irregular channel `266`. -/
theorem completeIrregularScan1381 :
    ∀ j ∈ indices 1381, (1381 : ℤ) ∣ (bernoulli j).num → j = 266 := by
  intro j hj hirregular
  have hmem : j ∈ ({266} : Finset ℕ) :=
    bernoulli_numerator_dvd_imp_mem_candidates
      (p := 1381) (a := 2) (by norm_num) (by norm_num)
      {266} scanResidue_ne_zero_outside_channel
      j hj hirregular
  simpa only [Finset.mem_singleton] using hmem

private theorem pow_367346_eq_bin (a : ZMod (1381 ^ 4)) :
    a ^ 367346 = npowBinRec 367346 a := by
  change npowRecAuto 367346 a = npowBinRecAuto 367346 a
  rw [npowRec_eq_npowBinRec]

/-- Kernel-checked provenance for the archive's lifted weight `561`.

The equality is the compact evaluator corresponding to
`P_367346(1381) = 561 * 1381^3` modulo `1381^4`. -/
theorem liftedPowerSum_eq_weight1381 :
    (∑ a ∈ Finset.range 1381,
      (a : ZMod (1381 ^ 4)) ^ 367346) =
        1381 * (((1381 ^ 2 * 561 : ℕ) : ZMod (1381 ^ 4))) := by
  norm_num only [Nat.cast_ofNat, Nat.reducePow]
  simp_rw [pow_367346_eq_bin]
  decide

/-- The unique lifted Bernoulli channel has valuation strictly below three. -/
theorem bernoulli_367346_numerator_not_dvd_cube :
    ¬(1381 : ℤ) ^ 3 ∣ (bernoulli 367346).num := by
  apply bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := 1381) (n := 367346) (c := 5982476711365)
      (r := 1381 ^ 2 * 561)
  · norm_num
  · norm_num
  · decide
  · norm_num
  · apply pIntegral_of_denominatorPrimeTo
    apply bernoulli_denominatorPrimeTo (p := 1381)
    · decide
    · norm_num
  · rw [← Nat.choose_symm (by norm_num : 367344 ≤ 367347)]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial]
  · exact liftedPowerSum_eq_weight1381
  · exact residue1381_ne_zero
  · exact residue1381_not_dvd_cube
  · apply bernoulli_denominatorPrimeTo (p := 1381)
    · decide
    · norm_num

/-- The compact moment receipt supplies the complete Case-II.2 Bernoulli
condition at exponent `1381`. -/
theorem bernoulliCubeCondition1381 : BernoulliCubeCondition 1381 := by
  apply bernoulliCubeCondition_of_irregular (by norm_num)
  intro j hj hirregular
  rw [completeIrregularScan1381 j hj hirregular]
  simpa using bernoulli_367346_numerator_not_dvd_cube

end Fermat.Certificates.CaseII_2.BernoulliMomentCertificate1381
