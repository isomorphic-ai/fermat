import Fermat.GenericIrregular.ExactFaulhaberValuation
import Fermat.GenericIrregular.WeightedMoment
import Fermat.Irregular.VandiverData

/-!
# Finite channel certificates for a fixed irregular exponent

This module separates the reusable proof from the finite arithmetic supplied
for one chosen prime `p`.

* A `LiftedPowerSumCertificate` records one direct Faulhaber computation.
* A `FixedChannelCertificate` records the complete finite family of irregular
  indices and one nonzero weighted-moment determinant.

The determinant is the sole simultaneous nonvanishing input.  The generic
weighted-moment theorem recovers every individual nonzero correction weight,
and the direct Faulhaber theorem then proves Vandiver's Bernoulli cube
condition in every channel.
-/

open scoped BigOperators

namespace Fermat.GenericIrregular.ChannelCertificate

open Fermat.GenericIrregular.WeightedMoment
open Fermat.Irregular

/-- The exact arithmetic attached to one lifted irregular index.

The power-sum residue is represented as `p^2 * correction` after the first
leading factor of `p` has been removed.  Its reduction modulo `p` is the
weight used by `WeightedMoment`. -/
structure LiftedPowerSumCertificate (p : ℕ) [Fact p.Prime] where
  index : ℕ
  chooseQuotient : ℕ
  correction : ℕ
  index_mem : index ∈ VandiverData.indices p
  target_ge_six : 6 ≤ index * p
  target_even : Even (index * p)
  denominator_next : ¬p ∣ index * p + 1
  previous_integral : DirectBernoulli.PIntegral p
    (bernoulli (index * p - 2))
  choose_eq :
    (index * p + 1).choose (index * p - 2) =
      p * chooseQuotient
  powerSum :
    (∑ a ∈ Finset.range p,
      (a : ZMod (p ^ 4)) ^ (index * p)) =
        p * ((p ^ 2 * correction : ℕ) : ZMod (p ^ 4))
  target_denominator :
    BernoulliData.DenominatorPrimeTo p
      (bernoulli (index * p))

namespace LiftedPowerSumCertificate

variable {p : ℕ} [Fact p.Prime]

/-- The correction coefficient reduced modulo the fixed prime. -/
def weight (C : LiftedPowerSumCertificate p) : ZMod p :=
  C.correction

private theorem correction_ne_zero
    (C : LiftedPowerSumCertificate p) (hweight : C.weight ≠ 0) :
    C.correction ≠ 0 := by
  intro hzero
  apply hweight
  simp [weight, hzero]

private theorem correction_not_dvd
    (C : LiftedPowerSumCertificate p) (hweight : C.weight ≠ 0) :
    ¬p ∣ C.correction := by
  intro hdvd
  apply hweight
  exact (ZMod.natCast_eq_zero_iff C.correction p).2 hdvd

private theorem residue_ne_zero
    (C : LiftedPowerSumCertificate p) (hweight : C.weight ≠ 0) :
    p ^ 2 * C.correction ≠ 0 :=
  mul_ne_zero (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)
    (C.correction_ne_zero hweight)

private theorem residue_not_dvd_cube
    (C : LiftedPowerSumCertificate p) (hweight : C.weight ≠ 0) :
    ¬(p : ℤ) ^ 3 ∣ (p ^ 2 * C.correction : ℕ) := by
  intro hcube
  apply C.correction_not_dvd hweight
  have hp2 : (p : ℤ) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (Int.natCast_ne_zero.mpr
      (Fact.out : p.Prime).ne_zero)
  have hcancel :
      (p : ℤ) ^ 2 * p ∣
        (p : ℤ) ^ 2 * C.correction := by
    simpa only [pow_succ, Int.natCast_mul, Int.natCast_pow] using hcube
  have hdvdInt : (p : ℤ) ∣ C.correction :=
    (mul_dvd_mul_iff_left hp2).mp hcancel
  exact_mod_cast hdvdInt

/-- A nonzero correction modulo `p` makes the full Faulhaber residue have
valuation exactly two. -/
private theorem residue_padicValRat_eq_two
    (C : LiftedPowerSumCertificate p) (hweight : C.weight ≠ 0) :
    padicValRat p ((p ^ 2 * C.correction : ℕ) : ℚ) = 2 := by
  have hp0 : (p : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hc0 : (C.correction : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (C.correction_ne_zero hweight)
  have hcorrectionVal :
      padicValRat p (C.correction : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    exact_mod_cast
      padicValNat.eq_zero_of_not_dvd (C.correction_not_dvd hweight)
  rw [Nat.cast_mul, Nat.cast_pow,
    padicValRat.mul (pow_ne_zero 2 hp0) hc0,
    padicValRat.pow hp0, padicValRat.of_nat,
    padicValNat_self, hcorrectionVal]
  norm_num

/-- Exact form of the lifted-channel conclusion: the Bernoulli number has
precisely two factors of `p`. -/
theorem bernoulli_padicValRat_eq_two
    (C : LiftedPowerSumCertificate p) (hp5 : 5 ≤ p)
    (hweight : C.weight ≠ 0) :
    padicValRat p (bernoulli (C.index * p)) = 2 := by
  exact
    ExactFaulhaberValuation.bernoulli_padicValRat_eq_two_of_faulhaber
      hp5 C.target_ge_six C.target_even C.denominator_next
      C.previous_integral C.choose_eq C.powerSum
      (C.residue_ne_zero hweight)
      (C.residue_padicValRat_eq_two hweight)

/-- A nonzero compressed weight closes its lifted Bernoulli channel. -/
theorem bernoulli_numerator_not_dvd_cube
    (C : LiftedPowerSumCertificate p) (hp5 : 5 ≤ p)
    (hweight : C.weight ≠ 0) :
    ¬(p : ℤ) ^ 3 ∣ (bernoulli (C.index * p)).num := by
  apply
    DirectBernoulli.bernoulli_numerator_not_dvd_cube_of_faulhaber
      (p := p) (n := C.index * p)
      (c := C.chooseQuotient)
      (r := p ^ 2 * C.correction)
  · exact hp5
  · exact C.target_ge_six
  · exact C.target_even
  · exact C.denominator_next
  · exact C.previous_integral
  · exact C.choose_eq
  · exact C.powerSum
  · exact C.residue_ne_zero hweight
  · exact C.residue_not_dvd_cube hweight
  · exact C.target_denominator

end LiftedPowerSumCertificate

variable {p N : ℕ} [Fact p.Prime]

/-- Levels of a finite channel family, reduced modulo `p`. -/
def levels (channel : Fin N → LiftedPowerSumCertificate p) :
    Fin N → ZMod p :=
  fun i ↦ (channel i).index

/-- Weights of a finite channel family, reduced modulo `p`. -/
def weights (channel : Fin N → LiftedPowerSumCertificate p) :
    Fin N → ZMod p :=
  fun i ↦ (channel i).weight

/-- The complete finite correction certificate at one chosen prime.

No second-case conclusion is stored here.  The fields are the complete
low-index scan, distinctness of its indices, the per-channel power sums, and
one nonzero axis-8 determinant. -/
structure FixedChannelCertificate (p N : ℕ) [Fact p.Prime] where
  channel : Fin N → LiftedPowerSumCertificate p
  index_injective : Function.Injective (fun i ↦ (channel i).index)
  complete :
    ∀ j ∈ VandiverData.indices p,
      (p : ℤ) ∣ (bernoulli j).num →
        ∃ i, j = (channel i).index
  moment_nondegenerate :
    (weightedMoment (levels channel) (weights channel)).det ≠ 0

namespace FixedChannelCertificate

/-- Indices in Vandiver's range are strictly below `p`. -/
private theorem index_lt
    (C : FixedChannelCertificate p N) (hp5 : 5 ≤ p) (i : Fin N) :
    (C.channel i).index < p := by
  have hi : 2 ≤ (C.channel i).index ∧
      (C.channel i).index ≤ p - 3 ∧
        Even (C.channel i).index := by
    simpa [VandiverData.indices, and_assoc] using
      (C.channel i).index_mem
  omega

/-- Distinct integer indices remain distinct levels modulo `p`. -/
theorem levels_injective
    (C : FixedChannelCertificate p N) (hp5 : 5 ≤ p) :
    Function.Injective (levels C.channel) := by
  intro i j hij
  apply C.index_injective
  have hval := congrArg ZMod.val hij
  simpa [levels, ZMod.val_natCast_of_lt (C.index_lt hp5 i),
    ZMod.val_natCast_of_lt (C.index_lt hp5 j)] using hval

/-- The single axis-8 determinant proves every correction weight nonzero. -/
theorem weight_ne_zero
    (C : FixedChannelCertificate p N) (hp5 : 5 ≤ p) (i : Fin N) :
    weights C.channel i ≠ 0 :=
  weight_ne_zero_of_det_weightedMoment_ne_zero
    (C.levels_injective hp5) C.moment_nondegenerate i

/-- A complete scan and one nonzero moment determinant imply the full finite
Bernoulli condition used by Vandiver's second-case descent. -/
theorem bernoulliCubeCondition
    (C : FixedChannelCertificate p N) (hp5 : 5 ≤ p) :
    VandiverData.BernoulliCubeCondition p := by
  apply VandiverData.bernoulliCubeCondition_of_irregular hp5
  intro j hj hirregular
  obtain ⟨i, rfl⟩ := C.complete j hj hirregular
  exact
    (C.channel i).bernoulli_numerator_not_dvd_cube hp5
      (C.weight_ne_zero hp5 i)

end FixedChannelCertificate

end Fermat.GenericIrregular.ChannelCertificate
