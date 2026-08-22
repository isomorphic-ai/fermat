import Fermat.Descent.GenericIrregular.WeightedMoment
import Fermat.Descent.Irregular.LowFaulhaber
import Fermat.Descent.Irregular.ModularBernoulliScan
import Fermat.Descent.Irregular.SunCongruence
import Fermat.Exponents.OneThousandThreeHundredEightyOne.IrregularScanCertificate

/-!
# Weighted Bernoulli moment certificate at exponent 1381

This module is the finite Case-II.2 receipt supplied by
`flt8-moment-1381.zip` (archive SHA-256
`02c8a98d90c444b72b0b3d9844ccb20af47196fead57ac75d3da102779f1679c`).

The low scan leaves `266` as the sole possible irregular channel.  Its
centered level is `0`, and its normalized lifted weight is `561` modulo
`1381`.  Thus the weighted moment matrix is the one-by-one matrix `[[561]]`.

The determinant proves nonvanishing of the supplied weight.  Its provenance
now comes from two low contacts, at indices `266` and `1646`, followed by
Sun's depth-two interpolation to `266 * 1381 = 367346`.  No power sum at the
lifted index is evaluated.  Consequently this module does not import the
older exponent-local `PowerSumCertificates`, `HighBernoulli`, `IrregularScan`,
`GenericChannels`, or `VandiverData` assembly modules.
-/

open scoped BigOperators

namespace Fermat.Certificates.CaseII_2.BernoulliMomentCertificate1381

open Fermat.GenericIrregular.WeightedMoment
open Fermat.Irregular
open Fermat.Irregular.BernoulliData
open Fermat.Irregular.DirectBernoulli
open Fermat.Irregular.LowFaulhaber
open Fermat.Irregular.ModularBernoulliScan
open Fermat.Irregular.SunCongruence
open Fermat.Irregular.VandiverData
open Fermat.Irregular.Voronoi
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

private theorem pIntegral_div_prime_pow_of_hasPadicValAtLeast
    {p e : ℕ} [Fact p.Prime] {x : ℚ}
    (hx : HasPadicValAtLeast p (e : ℤ) x) :
    PIntegral p (x / (p : ℚ) ^ e) := by
  by_cases hx0 : x = 0
  · simp [hx0, PIntegral]
  rcases hx with hxzero | hxval
  · exact (hx0 hxzero).elim
  · rw [PIntegral, padicValRat.div hx0
      (pow_ne_zero e (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)),
      padicValRat.pow (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero),
      padicValRat.self (Fact.out : p.Prime).one_lt]
    norm_num
    exact hxval

private theorem pow_266_eq_bin (a : ZMod (1381 ^ 3)) :
    a ^ 266 = npowBinRec 266 a := by
  change npowRecAuto 266 a = npowBinRecAuto 266 a
  rw [npowRec_eq_npowBinRec]

private theorem pow_1646_eq_bin (a : ZMod (1381 ^ 3)) :
    a ^ 1646 = npowBinRec 1646 a := by
  change npowRecAuto 1646 a = npowBinRecAuto 1646 a
  rw [npowRec_eq_npowBinRec]

/-- First low contact: `P_266(1381) = 506 * 1381^2 (mod 1381^3)`. -/
theorem powerSum266_mod_cube :
    (∑ a ∈ Finset.range 1381,
      (a : ZMod (1381 ^ 3)) ^ 266) =
        1381 * (((1381 * 506 : ℕ) : ZMod (1381 ^ 3))) := by
  simp_rw [pow_266_eq_bin]
  decide

/-- Second low contact: `P_1646(1381) = 1267 * 1381^2 (mod 1381^3)`. -/
theorem powerSum1646_mod_cube :
    (∑ a ∈ Finset.range 1381,
      (a : ZMod (1381 ^ 3)) ^ 1646) =
        1381 * (((1381 * 1267 : ℕ) : ZMod (1381 ^ 3))) := by
  simp_rw [pow_1646_eq_bin]
  decide

private theorem bernoulli264_pIntegral : PIntegral 1381 (bernoulli 264) := by
  apply pIntegral_of_denominatorPrimeTo
  apply bernoulli_denominatorPrimeTo (p := 1381)
  · decide
  · norm_num

private theorem bernoulli1644_pIntegral : PIntegral 1381 (bernoulli 1644) := by
  apply pIntegral_of_denominatorPrimeTo
  apply bernoulli_denominatorPrimeTo (p := 1381)
  · decide
  · norm_num

/-- `B_266 = 1381 * 506 (mod 1381^2)`, with a p-integral error. -/
theorem bernoulli266_lowContact :
    ∃ u : ℚ, PIntegral 1381 u ∧
      bernoulli 266 = 1381 * 506 + (1381 : ℚ) ^ 2 * u := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (bernoulli_representation_of_powerSum_cube
      (p := 1381) (n := 266) (r := 1381 * 506)
      (by norm_num) (by norm_num) (by decide) (by norm_num)
      bernoulli264_pIntegral (by simpa using powerSum266_mod_cube))

/-- `B_1646 = 1381 * 1267 (mod 1381^2)`, with a p-integral error. -/
theorem bernoulli1646_lowContact :
    ∃ u : ℚ, PIntegral 1381 u ∧
      bernoulli 1646 = 1381 * 1267 + (1381 : ℚ) ^ 2 * u := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (bernoulli_representation_of_powerSum_cube
      (p := 1381) (n := 1646) (r := 1381 * 1267)
      (by norm_num) (by norm_num) (by decide) (by norm_num)
      bernoulli1644_pIntegral (by simpa using powerSum1646_mod_cube))

/-- The production Sun theorem specialized to `(p,b,k) = (1381,266,266)`. -/
theorem sunCongruence1381 :
    RationalModEq 1381 2
      (bernoulli 367346 / (367346 : ℚ))
      (266 * (bernoulli 1646 / (1646 : ℚ)) -
        265 * (1 - (1381 : ℚ) ^ 265) *
          (bernoulli 266 / (266 : ℚ))) := by
  convert sunCongruence
      (p := 1381) (b := 266) (k := 266)
      (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num)
    using 1
  all_goals norm_num [sunIndex]

/-- Normalized first contact:
`B_266 / 266 = 1381 * 1196 (mod 1381^2)`. -/
theorem bernoulli266_div_normalized :
    ∃ u : ℚ, PIntegral 1381 u ∧
      bernoulli 266 / (266 : ℚ) =
        1381 * 1196 + (1381 : ℚ) ^ 2 * u := by
  obtain ⟨u, hu, hB⟩ := bernoulli266_lowContact
  refine ⟨u / 266 - (230 : ℚ) / 266, ?_, ?_⟩
  · exact pIntegral_sub
      (pIntegral_div_nat hu (by norm_num) (by norm_num))
      (pIntegral_div_nat (pIntegral_nat 1381 230)
        (by norm_num) (by norm_num))
  · rw [hB]
    ring_nf

/-- Normalized second contact:
`B_1646 / 1646 = 1381 * 750 (mod 1381^2)`. -/
theorem bernoulli1646_div_normalized :
    ∃ u : ℚ, PIntegral 1381 u ∧
      bernoulli 1646 / (1646 : ℚ) =
        1381 * 750 + (1381 : ℚ) ^ 2 * u := by
  obtain ⟨u, hu, hB⟩ := bernoulli1646_lowContact
  refine ⟨u / 1646 - (893 : ℚ) / 1646, ?_, ?_⟩
  · exact pIntegral_sub
      (pIntegral_div_nat hu (by norm_num) (by norm_num))
      (pIntegral_div_nat (pIntegral_nat 1381 893)
        (by norm_num) (by norm_num))
  · rw [hB]
    ring_nf

/-- The right side of Sun's congruence for the 1381 channel. -/
def sunRhs1381 : ℚ :=
  266 * (bernoulli 1646 / (1646 : ℚ)) -
    265 * (1 - (1381 : ℚ) ^ 265) *
      (bernoulli 266 / (266 : ℚ))

/-- The two low contacts evaluate Sun's right side to
`1381 * 1326 (mod 1381^2)`. -/
theorem sunRhs1381_representation :
    ∃ u : ℚ, PIntegral 1381 u ∧
      sunRhs1381 = 1381 * 1326 + (1381 : ℚ) ^ 2 * u := by
  obtain ⟨u0, hu0, h0⟩ := bernoulli266_div_normalized
  obtain ⟨u1, hu1, h1⟩ := bernoulli1646_div_normalized
  let u : ℚ :=
    (-86 : ℚ) + 266 * u1 - 265 * u0 +
      265 * (1381 : ℚ) ^ 264 * 1196 +
      265 * (1381 : ℚ) ^ 265 * u0
  refine ⟨u, ?_, ?_⟩
  · dsimp only [u]
    have hbase : PIntegral 1381
        ((-86 : ℚ) + 266 * u1 - 265 * u0) :=
      pIntegral_sub
        (pIntegral_add (pIntegral_int 1381 (-86))
          (pIntegral_mul (pIntegral_nat 1381 266) hu1))
        (pIntegral_mul (pIntegral_nat 1381 265) hu0)
    have hhigh0 : PIntegral 1381
        (265 * (1381 : ℚ) ^ 264 * 1196) := by
      exact_mod_cast pIntegral_nat 1381 (265 * 1381 ^ 264 * 1196)
    have hhigh1 : PIntegral 1381
        (265 * (1381 : ℚ) ^ 265 * u0) := by
      exact pIntegral_mul
        (by exact_mod_cast pIntegral_nat 1381 (265 * 1381 ^ 265)) hu0
    exact pIntegral_add (pIntegral_add hbase hhigh0) hhigh1
  · dsimp only [sunRhs1381, u]
    rw [h1, h0]
    rw [show (1381 : ℚ) ^ 265 = (1381 : ℚ) ^ 264 * 1381 by
      rw [show 265 = 264 + 1 by omega, pow_succ]]
    set_option exponentiation.threshold 300 in
      ring

/-- Sun interpolation and the low contacts determine the normalized lifted
Bernoulli quotient modulo `1381^2`. -/
theorem highQuotient1381_representation :
    ∃ u : ℚ, PIntegral 1381 u ∧
      bernoulli 367346 / (367346 : ℚ) =
        1381 * 1326 + (1381 : ℚ) ^ 2 * u := by
  obtain ⟨u, hu, hRhs⟩ := sunRhs1381_representation
  have hdiff : HasPadicValAtLeast 1381 2
      (bernoulli 367346 / (367346 : ℚ) - sunRhs1381) := by
    simpa only [sunRhs1381, PadicValAtLeast, HasPadicValAtLeast,
      Nat.cast_ofNat] using sunCongruence1381.2.2
  let d : ℚ :=
    (bernoulli 367346 / (367346 : ℚ) - sunRhs1381) /
      (1381 : ℚ) ^ 2
  have hd : PIntegral 1381 d :=
    pIntegral_div_prime_pow_of_hasPadicValAtLeast hdiff
  have hdiffEq :
      bernoulli 367346 / (367346 : ℚ) - sunRhs1381 =
        (1381 : ℚ) ^ 2 * d := by
    dsimp only [d]
    field_simp
  refine ⟨u + d, pIntegral_add hu hd, ?_⟩
  calc
    bernoulli 367346 / (367346 : ℚ) =
        sunRhs1381 +
          (bernoulli 367346 / (367346 : ℚ) - sunRhs1381) := by ring
    _ = sunRhs1381 + (1381 : ℚ) ^ 2 * d := by rw [hdiffEq]
    _ = 1381 * 1326 + (1381 : ℚ) ^ 2 * (u + d) := by
      rw [hRhs]
      ring

/-- Exact provenance for the archived weight: after removing `1381^2`,
the lifted Bernoulli number is `561` modulo `1381`. -/
theorem bernoulli367346_weight561 :
    ∃ u : ℚ, PIntegral 1381 u ∧
      bernoulli 367346 =
        (1381 : ℚ) ^ 2 * 561 + (1381 : ℚ) ^ 3 * u := by
  obtain ⟨u, hu, hQ⟩ := highQuotient1381_representation
  let v : ℚ := 255 + 266 * u
  refine ⟨v, ?_, ?_⟩
  · exact pIntegral_add (pIntegral_nat 1381 255)
      (pIntegral_mul (pIntegral_nat 1381 266) hu)
  · dsimp only [v]
    have h := congrArg (fun q : ℚ ↦ (367346 : ℚ) * q) hQ
    field_simp at h ⊢
    linear_combination h

/-- The moment entry is the actual normalized lifted Bernoulli residue, not
merely a nonzero proxy. -/
theorem liftedWeight1381_authenticated :
    ∃ u : ℚ, PIntegral 1381 u ∧
      bernoulli 367346 =
        (1381 : ℚ) ^ 2 * ((liftedWeight1381 0).val : ℚ) +
          (1381 : ℚ) ^ 3 * u := by
  have hval : (liftedWeight1381 0).val = 561 := by decide
  rw [hval]
  exact bernoulli367346_weight561

private theorem weightResidue1381_not_dvd : ¬1381 ∣ 561 := by
  intro hdvd
  apply liftedWeight1381_ne_zero 0
  exact (ZMod.natCast_eq_zero_iff 561 1381).2 hdvd

private theorem padicValRat_weightResidue1381 :
    padicValRat 1381 (((1381 ^ 2 * 561 : ℕ) : ℚ)) = 2 := by
  rw [Nat.cast_mul, Nat.cast_pow,
    padicValRat.mul (pow_ne_zero 2 (by norm_num)) (by norm_num),
    padicValRat.pow (by norm_num),
    padicValRat.self (by norm_num),
    padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd weightResidue1381_not_dvd]
  norm_num

/-- The authenticated moment coefficient gives exact valuation two for the
lifted Bernoulli number. -/
theorem bernoulli367346_padicValRat_eq_two :
    padicValRat 1381 (bernoulli 367346) = 2 := by
  obtain ⟨u, hu, hB⟩ := bernoulli367346_weight561
  have hB' : bernoulli 367346 =
      (((1381 ^ 2 * 561 : ℕ) : ℚ)) + (1381 : ℚ) ^ 3 * u := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hB
  have result := representation_ne_zero_and_padicValRat_eq
    (p := 1381) (r := 1381 ^ 2 * 561)
    (by norm_num) hu hB'
    (by rw [padicValRat_weightResidue1381]; omega)
  rw [result.2, padicValRat_weightResidue1381]

/-- The unique lifted Bernoulli channel has valuation strictly below three. -/
theorem bernoulli_367346_numerator_not_dvd_cube :
    ¬(1381 : ℤ) ^ 3 ∣ (bernoulli 367346).num := by
  apply numerator_not_dvd_pow_of_padicValRat_lt
    (p := 1381) (n := 3)
  · intro hzero
    have hval := bernoulli367346_padicValRat_eq_two
    rw [hzero, padicValRat.zero] at hval
    omega
  · apply bernoulli_denominatorPrimeTo (p := 1381)
    · decide
    · norm_num
  · rw [bernoulli367346_padicValRat_eq_two]
    omega

/-- Arithmetic identification of Sun's quotient residue with the archive's
lifted Bernoulli weight. -/
theorem sun_weight_eq_archive_weight :
    ((266 : ZMod 1381) * 1326) = 561 := by
  decide

/-- The compact moment receipt supplies the complete Case-II.2 Bernoulli
condition at exponent `1381`. -/
theorem bernoulliCubeCondition1381 : BernoulliCubeCondition 1381 := by
  apply bernoulliCubeCondition_of_irregular (by norm_num)
  intro j hj hirregular
  rw [completeIrregularScan1381 j hj hirregular]
  simpa using bernoulli_367346_numerator_not_dvd_cube

end Fermat.Certificates.CaseII_2.BernoulliMomentCertificate1381
