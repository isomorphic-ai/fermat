/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Complementary Dwork coefficient at 59

The depth-15 and depth-44 Dwork parameters meet for the first time in total
depth `59`.  This file computes that first complementary term on both sides
of the available coordinate bridge.

On the formal-logarithm side, the coefficient of
`log(1 + X^15) * d log(1 + X^44)` in degree `58` is exactly `44`; the reverse
orientation gives `15`, and their alternating difference is `29`.  On the
Dwork side, multiplication of the two parameter coordinates is exactly
`59` times a normalized term.  That term is congruent to `-pi` to very high
parameter-adic order, has exact parameter depth one, and has first Dwork
basis coefficient `-1` modulo `59`.

Finally, every one of the `58 x 58` translated products is identified with
its Teichmuller scale, and the two normalized character projectors preserve
an arbitrary scalar coefficient.  In particular they preserve the nonzero
formal coefficient `44`.

This is the strongest coefficient-side input presently available for the
Kummer--Artin / Hilbert-symbol comparison.  It deliberately does not claim
that the continuous local cup readout equals this coefficient.  That map
comparison remains a separate arithmetic theorem, in agreement with
`7A-ARTIN-READ.md`.
-/
import Fermat.FiftyNine.Conservation.DworkProjectorUnitRepresentative59
import Fermat.Conservation.GuardDependsOn
import KummerCriterion.CyclotomicUnits.KummerLogCoefficient.Coordinates
import Mathlib.RingTheory.PowerSeries.Log

open scoped BigOperators NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.DworkComplementaryArtinHasse59

set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

open Fermat.FiftyNine.Conservation.AdicCompleteValuedInteger59
open Fermat.FiftyNine.Conservation.DworkPrincipalUnitCandidates59
open Fermat.FiftyNine.Conservation.DworkProjectorUnitRepresentative59
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open KummerCriterion.CyclotomicUnits
open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter.Conjugation
open PowerSeries

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

noncomputable local instance instGaloisIndex59CardInvertibleZMod :
    Invertible (Fintype.card GaloisIndex59 : ZMod 59) :=
  invertibleOfNonzero (by
    rw [galoisIndex59_card]
    decide)

/-! ## The formal complementary logarithmic coefficient -/

/-- The formal logarithm with its parameter placed in Dwork depth `depth`.
Only the positive depths `15` and `44` are used below. -/
noncomputable def formalLogarithmAtDworkDepth59 (depth : ℕ) :
    PowerSeries ℚ :=
  PowerSeries.subst (PowerSeries.X ^ depth) (PowerSeries.log ℚ)

/-- The first complementary coefficient in the `15` then `44`
orientation is exactly `44`. -/
theorem formalLogDifferentialCoefficient_fifteen_fortyFour59 :
    PowerSeries.coeff 58
        (formalLogarithmAtDworkDepth59 15 *
          (d⁄dX ℚ) (formalLogarithmAtDworkDepth59 44)) = 44 := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [formalLogarithmAtDworkDepth59,
    PowerSeries.coeff_derivative, PowerSeries.coeff_subst_X_pow,
    PowerSeries.coeff_log, Finset.sum_range_succ]

/-- Reversing the two depths gives the complementary coefficient `15`. -/
theorem formalLogDifferentialCoefficient_fortyFour_fifteen59 :
    PowerSeries.coeff 58
        (formalLogarithmAtDworkDepth59 44 *
          (d⁄dX ℚ) (formalLogarithmAtDworkDepth59 15)) = 15 := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [formalLogarithmAtDworkDepth59,
    PowerSeries.coeff_derivative, PowerSeries.coeff_subst_X_pow,
    PowerSeries.coeff_log, Finset.sum_range_succ]

/-- The alternating orientation retains the nonzero residue `44 - 15 = 29`.
This is recorded without asserting which orientation a future local-symbol
comparison will choose. -/
theorem formalAlternatingLogDifferentialCoefficient59 :
    PowerSeries.coeff 58
        (formalLogarithmAtDworkDepth59 15 *
            (d⁄dX ℚ) (formalLogarithmAtDworkDepth59 44) -
          formalLogarithmAtDworkDepth59 44 *
            (d⁄dX ℚ) (formalLogarithmAtDworkDepth59 15)) = 29 := by
  rw [map_sub, formalLogDifferentialCoefficient_fifteen_fortyFour59,
    formalLogDifferentialCoefficient_fortyFour_fifteen59]
  norm_num

/-! ## The normalized Dwork cross term -/

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- The integral Dwork term left after dividing the complementary product
`pi^15 * pi^44` by `59`. -/
noncomputable def dworkComplementaryNormalizedTerm59 :
    DworkCompleteIntegerRing 59 K :=
  dworkRamificationUnit (p := 59) (K := K) (by norm_num) *
    dworkParameter 59 K

/-- Complementary depths multiply to exactly `59` times the normalized
cross term. -/
theorem dworkParameter_fifteen_mul_fortyFour59 :
    dworkParameter 59 K ^ 15 * dworkParameter 59 K ^ 44 =
      (59 : DworkCompleteIntegerRing 59 K) *
        dworkComplementaryNormalizedTerm59 K := by
  rw [← pow_add]
  norm_num
  simpa [dworkComplementaryNormalizedTerm59] using
    (natCast_prime_mul_dworkRamificationCorrection
      (p := 59) (K := K) (by norm_num)
      (1 : DworkCompleteIntegerRing 59 K)).symm

/-- The same identity stated directly for the nonconstant coordinates of
the two Dwork principal units. -/
theorem dworkPrincipalUnit_coordinates_fifteen_mul_fortyFour59 :
    ((dworkPrincipalUnitFifteen59 K : DworkCompleteIntegerRing 59 K) - 1) *
        ((dworkPrincipalUnitFortyFour59 K :
            DworkCompleteIntegerRing 59 K) - 1) =
      (59 : DworkCompleteIntegerRing 59 K) *
        dworkComplementaryNormalizedTerm59 K := by
  rw [dworkPrincipalUnitFifteen59, dworkPrincipalUnitFortyFour59,
    dworkPrincipalUnitAtDepth59_sub_one,
    dworkPrincipalUnitAtDepth59_sub_one]
  exact dworkParameter_fifteen_mul_fortyFour59 K

/-- The normalized term is congruent to `-pi` beyond the full Dwork basis
range. -/
theorem dworkComplementaryNormalizedTerm59_add_parameter_mem_tail :
    dworkComplementaryNormalizedTerm59 K + dworkParameter 59 K ∈
      (dworkParameterIdeal 59 K) ^ ((59 - 1) ^ 2 + 1) := by
  have heps :=
    dworkRamificationUnit_add_one_mem_dworkParameterIdeal_pow_tail
      (p := 59) (K := K) (by norm_num)
  have hpi : dworkParameter 59 K ∈ (dworkParameterIdeal 59 K) ^ 1 := by
    simp [dworkParameterIdeal]
  have hmul := Ideal.mul_mem_mul heps hpi
  rw [← pow_add] at hmul
  convert hmul using 1
  · simp [dworkComplementaryNormalizedTerm59]
    ring

/-- The cyclotomic uniformizer has exact lambda-adic depth one. -/
theorem valuedCyclotomicLambdaInteger59_not_mem_sq :
    valuedCyclotomicLambdaInteger 59 K ∉ (lambdaIdeal 59 K) ^ 2 := by
  intro hmem
  have hle := norm_le_norm_lambda_pow_of_mem K 2 hmem
  have hlt := norm_valuedCyclotomicLambdaInteger_lt_one K
  have hpos : 0 < ‖valuedCyclotomicLambdaInteger 59 K‖ :=
    norm_pos_iff.mpr
      (valuedCyclotomicLambdaInteger_ne_zero (p := 59) (K := K))
  rw [norm_pow] at hle
  nlinarith

/-- The Dwork parameter also has exact parameter-adic depth one. -/
theorem dworkParameter59_not_mem_sq :
    dworkParameter 59 K ∉ (dworkParameterIdeal 59 K) ^ 2 := by
  intro hmem
  have heval := dworkComplete_evalₐ_eq_zero_of_mem_lambdaIdeal_pow
    (p := 59) (K := K) (by
      simpa [dworkParameterIdeal_eq_dworkCompleteLambdaIdeal] using hmem)
  rw [dworkParameter_evalₐ_two] at heval
  exact valuedCyclotomicLambdaInteger59_not_mem_sq K
    (Ideal.Quotient.eq_zero_iff_mem.mp heval)

/-- The normalized complementary term has exact parameter-adic depth one;
the division by `59` has not erased its first layer. -/
theorem dworkComplementaryNormalizedTerm59_not_mem_sq :
    dworkComplementaryNormalizedTerm59 K ∉
      (dworkParameterIdeal 59 K) ^ 2 := by
  intro hnorm
  have hdeep := dworkComplementaryNormalizedTerm59_add_parameter_mem_tail K
  have hsum :
      dworkComplementaryNormalizedTerm59 K + dworkParameter 59 K ∈
        (dworkParameterIdeal 59 K) ^ 2 :=
    Ideal.pow_le_pow_right (by norm_num) hdeep
  have hneg := ((dworkParameterIdeal 59 K) ^ 2).neg_mem hnorm
  apply dworkParameter59_not_mem_sq K
  convert ((dworkParameterIdeal 59 K) ^ 2).add_mem hsum hneg using 1
  ring

/-- The exact first Dwork power-basis coefficient of the normalized term is
`-1` modulo `59`. -/
theorem dworkComplementaryNormalizedTerm59_first_coefficient :
    rationalPadicIntegerToZMod 59
        ((dworkParameterPowerBasis 59 K).repr
          (dworkComplementaryNormalizedTerm59 K)
          (⟨1, by norm_num⟩ : Fin 58)) = -1 := by
  have hdeep := dworkComplementaryNormalizedTerm59_add_parameter_mem_tail K
  have hpred :
      dworkComplementaryNormalizedTerm59 K - (-dworkParameter 59 K) ∈
        (dworkParameterIdeal 59 K) ^ (59 - 1) := by
    simpa only [sub_neg_eq_add] using
      (Ideal.pow_le_pow_right
        (by norm_num : 59 - 1 ≤ (59 - 1) ^ 2 + 1) hdeep)
  have hcoord :=
    dworkParameterPowerBasis_coeff_zmod_eq_of_sub_mem_parameterIdeal_pow_pred
      (p := 59) (K := K) hpred (⟨1, by norm_num⟩ : Fin 58)
  rw [map_neg] at hcoord
  rw [show dworkParameter 59 K =
      dworkParameterPowerBasis 59 K (⟨1, by norm_num⟩ : Fin 58) by
        rw [dworkParameterPowerBasis_apply]
        simp] at hcoord
  simpa using hcoord

/-! ## Exact translated products -/

/-- The Teichmuller scale carried by the depth-15/depth-44 translated
parameter product indexed by `(sigma, tau)`. -/
noncomputable def dworkComplementaryOrbitScale59
    (sigma tau : GaloisIndex59) : RationalPadicIntegerRing 59 :=
  rationalPadicTeichmuller 59 (sigma : ZMod 59) ^ 15 *
    rationalPadicTeichmuller 59 (tau : ZMod 59) ^ 44

/-- Every translated complementary product is `59` times the same
normalized term, multiplied by its exact Teichmuller scale. -/
theorem dworkParameter_orbit_fifteen_mul_fortyFour59
    (sigma tau : GaloisIndex59) :
    dworkCompleteCyclotomicEquiv (p := 59) K sigma
          (dworkParameter 59 K ^ 15) *
        dworkCompleteCyclotomicEquiv (p := 59) K tau
          (dworkParameter 59 K ^ 44) =
      (59 : DworkCompleteIntegerRing 59 K) *
        (algebraMap (RationalPadicIntegerRing 59)
            (DworkCompleteIntegerRing 59 K)
            (dworkComplementaryOrbitScale59 sigma tau) *
          dworkComplementaryNormalizedTerm59 K) := by
  rw [dworkCompleteCyclotomicEquiv_dworkParameter_pow
      (p := 59) (K := K) (a := sigma)
      (i := (⟨15, by norm_num⟩ : Fin 58)),
    dworkCompleteCyclotomicEquiv_dworkParameter_pow
      (p := 59) (K := K) (a := tau)
      (i := (⟨44, by norm_num⟩ : Fin 58))]
  calc
    _ = ((algebraMap (RationalPadicIntegerRing 59)
            (DworkCompleteIntegerRing 59 K))
          (rationalPadicTeichmuller 59 (sigma : ZMod 59) ^ 15) *
        (algebraMap (RationalPadicIntegerRing 59)
            (DworkCompleteIntegerRing 59 K))
          (rationalPadicTeichmuller 59 (tau : ZMod 59) ^ 44)) *
          (dworkParameter 59 K ^ 15 * dworkParameter 59 K ^ 44) := by
        ring
    _ = _ := by
      rw [dworkParameter_fifteen_mul_fortyFour59 K]
      simp only [dworkComplementaryOrbitScale59, map_mul, map_pow]
      ring

/-- Reduction modulo `59` turns the exact Teichmuller scale into the two
power-character factors appearing in the finite projector orbit sum. -/
theorem dworkComplementaryOrbitScale59_mod_prime
    (sigma tau : GaloisIndex59) :
    rationalPadicIntegerToZMod 59
        (dworkComplementaryOrbitScale59 sigma tau) =
      ((powerCharacter59 15 sigma : (ZMod 59)ˣ) : ZMod 59) *
        ((powerCharacter59 44 tau : (ZMod 59)ˣ) : ZMod 59) := by
  simp [dworkComplementaryOrbitScale59, powerCharacter59]
  rw [show ((15 : ZMod 58).val) = 15 by decide]
  rw [show ((44 : ZMod 58).val) = 44 by decide]

/-! ## Fourier preservation of the complementary coefficient -/

/-- The normalized projector coefficients cancel the corresponding leading
power character exactly. -/
theorem projectorLeadingCharacterSum59_eq_one (t : ZMod 58) :
    ∑ sigma : GaloisIndex59,
      (projectorExponent59 t sigma : ZMod 59) *
        ((powerCharacter59 t sigma : (ZMod 59)ˣ) : ZMod 59) = 1 := by
  simp_rw [projectorExponent59, ZMod.natCast_zmod_val]
  simp only [mul_assoc, Units.val_inv_eq_inv_val]
  simp_rw [inv_mul_cancel₀ (Units.ne_zero _), mul_one]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_invOf_self (Fintype.card GaloisIndex59 : ZMod 59)

/-- The full `58 x 58` projector weight applied to a scalar coefficient.
This is a finite arithmetic object, not a local cup evaluation. -/
noncomputable def projectedComplementaryOrbitCoefficient59
    (coefficient : ZMod 59) : ZMod 59 :=
  ∑ tau : GaloisIndex59, ∑ sigma : GaloisIndex59,
    (projectorExponent59 44 tau : ZMod 59) *
      (projectorExponent59 15 sigma : ZMod 59) *
      ((powerCharacter59 15 sigma : (ZMod 59)ˣ) : ZMod 59) *
      ((powerCharacter59 44 tau : (ZMod 59)ˣ) : ZMod 59) * coefficient

/-- The complementary projector preserves every scalar coefficient exactly.
This is the finite cancellation law behind the predicted first term. -/
theorem projectedComplementaryOrbitCoefficient59_eq
    (coefficient : ZMod 59) :
    projectedComplementaryOrbitCoefficient59 coefficient = coefficient := by
  unfold projectedComplementaryOrbitCoefficient59
  have h15 := projectorLeadingCharacterSum59_eq_one (15 : ZMod 58)
  have h44 := projectorLeadingCharacterSum59_eq_one (44 : ZMod 58)
  calc
    _ = ∑ tau : GaloisIndex59,
        ((projectorExponent59 44 tau : ZMod 59) *
          ((powerCharacter59 44 tau : (ZMod 59)ˣ) : ZMod 59)) *
          (∑ sigma : GaloisIndex59,
            (projectorExponent59 15 sigma : ZMod 59) *
              ((powerCharacter59 15 sigma : (ZMod 59)ˣ) : ZMod 59)) *
          coefficient := by
      apply Finset.sum_congr rfl
      intro tau htau
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro sigma hsigma
      ring
    _ = ∑ tau : GaloisIndex59,
        ((projectorExponent59 44 tau : ZMod 59) *
          ((powerCharacter59 44 tau : (ZMod 59)ˣ) : ZMod 59)) *
          1 * coefficient := by
      rw [h15]
    _ = (∑ tau : GaloisIndex59,
        (projectorExponent59 44 tau : ZMod 59) *
          ((powerCharacter59 44 tau : (ZMod 59)ˣ) : ZMod 59)) *
          coefficient := by
      simp_rw [mul_one]
      rw [Finset.sum_mul]
    _ = 1 * coefficient := by rw [h44]
    _ = coefficient := one_mul _

/-- The projected forward logarithmic-differential coefficient. -/
noncomputable def projectedDworkLogDifferentialCoefficient59 : ZMod 59 :=
  projectedComplementaryOrbitCoefficient59 44

/-- The full finite projector orbit preserves the forward coefficient `44`.
-/
theorem projectedDworkLogDifferentialCoefficient59_eq_fortyFour :
    projectedDworkLogDifferentialCoefficient59 = 44 := by
  exact projectedComplementaryOrbitCoefficient59_eq 44

/-- Consequently the fully projected complementary coefficient is nonzero
modulo `59`. -/
theorem projectedDworkLogDifferentialCoefficient59_ne_zero :
    projectedDworkLogDifferentialCoefficient59 ≠ 0 := by
  rw [projectedDworkLogDifferentialCoefficient59_eq_fortyFour]
  decide

/-! ## Kernel-trust and dependency audit -/

/--
info: 'Fermat.FiftyNine.Conservation.DworkComplementaryArtinHasse59.formalLogDifferentialCoefficient_fifteen_fortyFour59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms formalLogDifferentialCoefficient_fifteen_fortyFour59

/--
info: 'Fermat.FiftyNine.Conservation.DworkComplementaryArtinHasse59.dworkParameter_fifteen_mul_fortyFour59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkParameter_fifteen_mul_fortyFour59

/--
info: 'Fermat.FiftyNine.Conservation.DworkComplementaryArtinHasse59.dworkComplementaryNormalizedTerm59_not_mem_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkComplementaryNormalizedTerm59_not_mem_sq

/--
info: 'Fermat.FiftyNine.Conservation.DworkComplementaryArtinHasse59.dworkComplementaryNormalizedTerm59_first_coefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkComplementaryNormalizedTerm59_first_coefficient

/--
info: 'Fermat.FiftyNine.Conservation.DworkComplementaryArtinHasse59.dworkParameter_orbit_fifteen_mul_fortyFour59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkParameter_orbit_fifteen_mul_fortyFour59

/--
info: 'Fermat.FiftyNine.Conservation.DworkComplementaryArtinHasse59.projectedDworkLogDifferentialCoefficient59_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms projectedDworkLogDifferentialCoefficient59_ne_zero

/- The formal calculation genuinely uses both the logarithm coefficients and
the substitution-by-a-power formula. -/
#guard_depends_on
  formalLogDifferentialCoefficient_fifteen_fortyFour59,
  PowerSeries.coeff_log

#guard_depends_on
  formalLogDifferentialCoefficient_fifteen_fortyFour59,
  PowerSeries.coeff_subst_X_pow

/- Complementary-depth division is the committed Dwork ramification
identity, not a restated numerical certificate. -/
#guard_depends_on
  dworkParameter_fifteen_mul_fortyFour59,
  natCast_prime_mul_dworkRamificationCorrection

/- The retained first layer consumes the high-order ramification-unit
congruence. -/
#guard_depends_on
  dworkComplementaryNormalizedTerm59_add_parameter_mem_tail,
  dworkRamificationUnit_add_one_mem_dworkParameterIdeal_pow_tail

#guard_depends_on
  dworkComplementaryNormalizedTerm59_first_coefficient,
  dworkParameterPowerBasis_coeff_zmod_eq_of_sub_mem_parameterIdeal_pow_pred

/- Every orbit term uses the exact completed cyclotomic action. -/
#guard_depends_on
  dworkParameter_orbit_fifteen_mul_fortyFour59,
  dworkCompleteCyclotomicEquiv_dworkParameter_pow

/- The scale readback is the genuine Teichmuller reduction theorem. -/
#guard_depends_on
  dworkComplementaryOrbitScale59_mod_prime,
  rationalPadicIntegerToZMod_teichmuller

/- Projector preservation consumes the normalized Fourier cancellation, and
the final nonvanishing endpoint consumes that preservation theorem. -/
#guard_depends_on
  projectedComplementaryOrbitCoefficient59_eq,
  projectorLeadingCharacterSum59_eq_one

#guard_depends_on
  projectedDworkLogDifferentialCoefficient59_ne_zero,
  projectedComplementaryOrbitCoefficient59_eq

end Fermat.FiftyNine.Conservation.DworkComplementaryArtinHasse59
