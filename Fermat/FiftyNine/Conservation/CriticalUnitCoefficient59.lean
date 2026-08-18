/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The canonical scalar meter on the critical one-unit layer

For a depth-59 one-unit `u`, this module divides `u - 1` by `lambda^59`
and reduces the resulting integer modulo the maximal ideal.  Multiplication
of one-units becomes addition of residue coefficients, and the kernel is
proved to be exactly `U_60`.  Consequently `U_59 / U_60` is equivalent to
the additive group of the actual lambda residue field.

The explicit correction has raw coefficient `-1`.  Scaling by its inverse
gives a canonical normalized meter on which the correction reads `1`.
The pinned Dwork comparison also identifies the residue field with `ZMod 59`.
This is local algebra only: no reciprocity value, norm-filtration hyperplane,
provider, or assumption is introduced.
-/
import Fermat.FiftyNine.Conservation.CriticalUnitQuotient59
import Fermat.FiftyNine.Conservation.TwistedArtinHasse59
import Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59
import KummerCriterion.CyclotomicUnits.DworkParameter.Part12

open scoped NumberField WithZero

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59

open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
open Fermat.FiftyNine.Conservation.CriticalUnitQuotient59
open Fermat.FiftyNine.Conservation.TwistedArtinHasse59
open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

abbrev LambdaIntegerRing59 :=
  (lambdaPlace59 K).adicCompletionIntegers K

abbrev LambdaResidueRing59 :=
  LambdaIntegerRing59 K ⧸ IsLocalRing.maximalIdeal (LambdaIntegerRing59 K)

noncomputable instance lambdaResidueRing59Field :
    Field (LambdaResidueRing59 K) :=
  Ideal.Quotient.field (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K))

def criticalCoefficientIntegral59 (u : U59 K) : LambdaIntegerRing59 K :=
  ⟨(((u : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) /
      canonicalLambda59 K ^ 59, by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow,
      canonicalLambda59_valuation]
    have hu := u.property
    rw [mem_lambdaOneUnits] at hu
    calc
      Valued.v (((u : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) *
          (WithZero.exp (-1 : ℤ) ^ 59)⁻¹
          ≤ WithZero.exp (-((59 : ℕ) : ℤ)) *
              (WithZero.exp (-1 : ℤ) ^ 59)⁻¹ :=
            by gcongr
      _ = 1 := by norm_num [← WithZero.exp_nsmul]⟩

def criticalCoefficient59 (u : U59 K) : LambdaResidueRing59 K :=
  Ideal.Quotient.mk (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K))
    (criticalCoefficientIntegral59 K u)

theorem mem_lambdaMaximalIdeal59_iff (a : LambdaIntegerRing59 K) :
    a ∈ IsLocalRing.maximalIdeal (LambdaIntegerRing59 K) ↔
      Valued.v (a : LambdaField59 K) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem natCast59_eq_zero_in_lambdaResidue :
    (59 : LambdaResidueRing59 K) = 0 := by
  change Ideal.Quotient.mk
    (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K))
      (59 : LambdaIntegerRing59 K) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_lambdaMaximalIdeal59_iff]
  change Valued.v (59 : LambdaField59 K) < 1
  rw [natCast59_valuation, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

noncomputable instance lambdaResidueRing59CharP :
    CharP (LambdaResidueRing59 K) 59 :=
  (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 59)).mpr
    (natCast59_eq_zero_in_lambdaResidue K)

theorem exists_fin59_residue_representative
    (a : LambdaIntegerRing59 K) :
    ∃ i : Fin 59,
      Valued.v ((a : LambdaField59 K) - (i : ℤ)) ≤
        WithZero.exp (-1 : ℤ) := by
  exact
    exists_completion_fin_valuation_sub_le_exp_neg_one_of_valuation_le_one
      (p := 59) (K := K) (a : LambdaField59 K) a.property

theorem zmodCastHom_to_lambdaResidue_surjective :
    Function.Surjective
      (ZMod.castHom (dvd_refl 59) (LambdaResidueRing59 K) :
        ZMod 59 →+* LambdaResidueRing59 K) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨i, hi⟩ := exists_fin59_residue_representative K a
  refine ⟨(i : ZMod 59), ?_⟩
  change
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K))
        (i : LambdaIntegerRing59 K) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K)) a
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [mem_lambdaMaximalIdeal59_iff]
  change Valued.v ((i : LambdaField59 K) - (a : LambdaField59 K)) < 1
  rw [show (i : LambdaField59 K) - (a : LambdaField59 K) =
      -((a : LambdaField59 K) - (i : ℤ)) by norm_num, Valuation.map_neg]
  exact hi.trans_lt (by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num)

/-- The lambda residue field is canonically the prime field `ZMod 59`.
The comparison theorem from the pinned KummerCriterion package supplies the
degree-one residue representatives in the valuation completion. -/
noncomputable def zmodEquivLambdaResidue59 :
    ZMod 59 ≃+* LambdaResidueRing59 K :=
  RingEquiv.ofBijective
    (ZMod.castHom (dvd_refl 59) (LambdaResidueRing59 K))
    ⟨RingHom.injective _, zmodCastHom_to_lambdaResidue_surjective K⟩

theorem lambdaResidue_pow_fiftyNine (x : LambdaResidueRing59 K) :
    x ^ 59 = x := by
  apply (zmodEquivLambdaResidue59 K).symm.injective
  rw [map_pow]
  exact ZMod.pow_card _

/-! ## Transporting the pinned Dwork model to the actual local ring -/

/-- The integer-ring cast induced by the equality of the Fermat-side and
pinned KummerCriterion cyclotomic places. -/
noncomputable def valuedIntegerEquivLambdaInteger59 :
    ValuedIntegerRing 59 K ≃+* LambdaIntegerRing59 K :=
  RingEquiv.cast
    (R := fun v : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K) =>
      (v.adicCompletionIntegers K : Type _))
    (lambdaPlace59_eq_kummerCriterion K).symm

/-- The corresponding cast on the fraction-field completions. -/
noncomputable def valuedCompletionEquivLambdaField59 :
    ValuedCompletion 59 K ≃+* LambdaField59 K :=
  RingEquiv.cast (lambdaPlace59_eq_kummerCriterion K).symm

private theorem completionCast_embedding
    {v w : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)} (h : v = w) (x : K) :
    RingEquiv.cast
        (R := fun t : IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers K) => t.adicCompletion K) h
        (NumberField.FinitePlace.embedding v x) =
      NumberField.FinitePlace.embedding w x := by
  cases h
  rfl

theorem valuedCompletionEquivLambdaField59_lambda :
    valuedCompletionEquivLambdaField59 K
        (valuedCyclotomicLambda 59 K) = canonicalLambda59 K := by
  have hv : valuedCyclotomicLambda 59 K =
      NumberField.FinitePlace.embedding
        (KummerCriterion.Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum 59 K)
        (IsCyclotomicExtension.zeta 59 ℚ K - 1) := by
    rfl
  have hc : canonicalLambda59 K =
      NumberField.FinitePlace.embedding (lambdaPlace59 K)
        (IsCyclotomicExtension.zeta 59 ℚ K - 1) := by
    simp [canonicalLambda59, lambdaLocalPrimitiveRoot59, localPrimitiveRoot59,
      globalPrimitiveRoot59, localization59]
  rw [hv, hc]
  exact completionCast_embedding K
    (lambdaPlace59_eq_kummerCriterion K).symm _

theorem valuedIntegerEquivLambdaInteger59_coe
    (x : ValuedIntegerRing 59 K) :
    ((valuedIntegerEquivLambdaInteger59 K x : LambdaIntegerRing59 K) :
        LambdaField59 K) =
      valuedCompletionEquivLambdaField59 K
        (x : ValuedCompletion 59 K) := by
  unfold valuedIntegerEquivLambdaInteger59 valuedCompletionEquivLambdaField59
  have hplace := lambdaPlace59_eq_kummerCriterion K
  cases hplace
  rfl

/-- The integer-ring transport takes the pinned Dwork uniformizer to the
concrete Fermat-side uniformizer. -/
def canonicalLambdaInteger59 : LambdaIntegerRing59 K :=
  ⟨canonicalLambda59 K, by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      canonicalLambda59_valuation]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num⟩

theorem valuedIntegerEquivLambdaInteger59_lambda :
    valuedIntegerEquivLambdaInteger59 K
        (valuedCyclotomicLambdaInteger 59 K) =
      canonicalLambdaInteger59 K := by
  apply Subtype.ext
  rw [valuedIntegerEquivLambdaInteger59_coe]
  exact valuedCompletionEquivLambdaField59_lambda K

theorem canonicalLambda59_ne_zero : canonicalLambda59 K ≠ 0 := by
  intro hzero
  have hval := canonicalLambda59_valuation K
  rw [hzero, map_zero] at hval
  exact WithZero.exp_ne_zero hval.symm

/-- The integral ramification quotient `59 / lambda^58`. -/
def ramificationQuotientIntegral59 : LambdaIntegerRing59 K :=
  ⟨(59 : LambdaField59 K) / canonicalLambda59 K ^ 58, by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, natCast59_valuation,
      canonicalLambda59_valuation]
    norm_num [← WithZero.exp_nsmul]⟩

/-- The classical cyclotomic ramification quotient has residue `-1`.
The proof transports the already-compiled Dwork ramification unit back from
the redundant formal completion and compares its corrected parameter with
the concrete cyclotomic uniformizer. -/
theorem ramificationQuotientIntegral59_residue_eq_neg_one :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K))
        (ramificationQuotientIntegral59 K) =
      (-1 : LambdaResidueRing59 K) := by
  let D := DworkCompleteIntegerRing 59 K
  let e₀ : D ≃+* ValuedIntegerRing 59 K :=
    (AdicCompletion.ofAlgEquiv (lambdaIdeal 59 K)).symm.toRingEquiv
  let e : D ≃+* LambdaIntegerRing59 K :=
    e₀.trans (valuedIntegerEquivLambdaInteger59 K)
  let lamD : D := dworkCompleteLambda 59 K
  let lamR : LambdaIntegerRing59 K := canonicalLambdaInteger59 K
  let epsD : D := dworkRamificationUnit (p := 59) (K := K) (by norm_num)
  let epsR : LambdaIntegerRing59 K := e epsD
  obtain ⟨u, hu⟩ :=
    dworkParameter_eq_dworkCompleteLambda_mul_unit (p := 59) (K := K)
  let uR : (LambdaIntegerRing59 K)ˣ := Units.map e.toRingHom u
  have he_lam : e lamD = lamR := by
    calc
      e lamD = valuedIntegerEquivLambdaInteger59 K (e₀ lamD) := rfl
      _ = valuedIntegerEquivLambdaInteger59 K
          (valuedCyclotomicLambdaInteger 59 K) := by
            rw [show e₀ lamD = valuedCyclotomicLambdaInteger 59 K by
              exact AdicCompletion.ofAlgEquiv_symm_of
                (lambdaIdeal 59 K) (valuedCyclotomicLambdaInteger 59 K)]
      _ = lamR := valuedIntegerEquivLambdaInteger59_lambda K
  have hlamR0 : lamR ≠ 0 := by
    intro hzero
    apply canonicalLambda59_ne_zero K
    exact congrArg Subtype.val hzero
  have hlamD0 : lamD ≠ 0 := by
    intro hzero
    apply hlamR0
    rw [← he_lam, hzero, map_zero]
  have hdiff :=
    dworkParameter_sub_dworkCompleteLambda_mem_sq (p := 59) (K := K)
  rw [dworkCompleteLambdaIdeal_eq_span, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at hdiff
  obtain ⟨a, haSquare⟩ := hdiff
  have hu_dwork_factor : (u : D) - 1 = a * lamD := by
    apply e.injective
    apply mul_left_cancel₀ hlamR0
    calc
      lamR * e ((u : D) - 1) = e (dworkParameter 59 K - lamD) := by
        rw [map_sub, map_one, hu, map_sub, map_mul, he_lam]
        ring
      _ = e (a * lamD ^ 2) := congrArg e haSquare.symm
      _ = lamR * e (a * lamD) := by
        rw [map_mul, map_pow, map_mul, he_lam]
        ring
  have hu_factor :
      (uR : LambdaIntegerRing59 K) - 1 = e a * lamR := by
    change e (u : D) - 1 = e a * lamR
    rw [← map_one e, ← map_sub, hu_dwork_factor, map_mul, he_lam]
  have hu_sub_max :
      (uR : LambdaIntegerRing59 K) - 1 ∈
        IsLocalRing.maximalIdeal (LambdaIntegerRing59 K) := by
    rw [mem_lambdaMaximalIdeal59_iff, hu_factor]
    change Valued.v
        (((e a : LambdaIntegerRing59 K) : LambdaField59 K) *
          canonicalLambda59 K) < 1
    rw [map_mul, canonicalLambda59_valuation]
    calc
      Valued.v (((e a : LambdaIntegerRing59 K) : LambdaField59 K)) *
          WithZero.exp (-1 : ℤ) ≤
        1 * WithZero.exp (-1 : ℤ) := by
          gcongr
          exact (e a).property
      _ < 1 := by
        simp only [one_mul]
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        norm_num
  have heps_factor :
      ∃ a : D, epsR + 1 = e a * lamR := by
    have hepsTail :=
      dworkRamificationUnit_add_one_mem_dworkParameterIdeal_pow_tail
        (p := 59) (K := K) (by norm_num)
    let tailDepth : ℕ := (59 - 1) ^ 2
    have htailPos : 0 < tailDepth := by
      dsimp [tailDepth]
      norm_num
    have hepsTail' : epsD + 1 ∈ (dworkParameterIdeal 59 K) ^ tailDepth := by
      exact hepsTail
    rw [dworkParameterIdeal, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton'] at hepsTail'
    obtain ⟨b, hb⟩ := hepsTail'
    let a : D := b * dworkParameter 59 K ^ (tailDepth - 1)
    have ha : a * dworkParameter 59 K = epsD + 1 := by
      calc
        a * dworkParameter 59 K =
            b * (dworkParameter 59 K ^ (tailDepth - 1) *
              dworkParameter 59 K) := by ring
        _ = b * dworkParameter 59 K ^ tailDepth := by
          rw [← pow_succ, Nat.sub_add_cancel htailPos]
        _ = epsD + 1 := hb
    refine ⟨a * (u : D), ?_⟩
    change e epsD + 1 = e (a * (u : D)) * lamR
    rw [← map_one e, ← map_add, ← he_lam, ← map_mul]
    apply congrArg e
    rw [← ha, hu]
    ring
  have heps_add_max :
      epsR + 1 ∈ IsLocalRing.maximalIdeal (LambdaIntegerRing59 K) := by
    obtain ⟨a, ha⟩ := heps_factor
    rw [mem_lambdaMaximalIdeal59_iff, ha]
    change Valued.v
        (((e a : LambdaIntegerRing59 K) : LambdaField59 K) *
          canonicalLambda59 K) < 1
    rw [map_mul, canonicalLambda59_valuation]
    calc
      Valued.v (((e a : LambdaIntegerRing59 K) : LambdaField59 K)) *
          WithZero.exp (-1 : ℤ) ≤
        1 * WithZero.exp (-1 : ℤ) := by
          gcongr
          exact (e a).property
      _ < 1 := by
        simp only [one_mul]
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        norm_num
  have hramD := natCast_prime_mul_dworkRamificationUnit
    (p := 59) (K := K) (by norm_num)
  have hramR :
      (59 : LambdaIntegerRing59 K) * epsR =
        (lamR * (uR : LambdaIntegerRing59 K)) ^ 58 := by
    have hmapped := congrArg e hramD
    change e ((59 : D) * epsD) = e (dworkParameter 59 K ^ 58) at hmapped
    rw [map_mul, map_pow, hu, map_mul, he_lam] at hmapped
    have he59 : e (59 : D) = (59 : LambdaIntegerRing59 K) := map_ofNat e 59
    rw [he59] at hmapped
    simpa [epsR, uR] using hmapped
  have hramIntegral :
      ramificationQuotientIntegral59 K * epsR =
        (uR : LambdaIntegerRing59 K) ^ 58 := by
    apply Subtype.ext
    change
      ((59 : LambdaField59 K) /
          canonicalLambda59 K ^ 58) *
          (epsR : LambdaField59 K) =
        ((uR : LambdaIntegerRing59 K) : LambdaField59 K) ^ 58
    have hramField := congrArg Subtype.val hramR
    change
      (59 : LambdaField59 K) * (epsR : LambdaField59 K) =
        (canonicalLambda59 K *
          ((uR : LambdaIntegerRing59 K) : LambdaField59 K)) ^ 58 at hramField
    rw [mul_pow] at hramField
    rw [div_mul_eq_mul_div, hramField]
    exact mul_div_cancel_left₀ _ (pow_ne_zero 58 (canonicalLambda59_ne_zero K))
  let q : LambdaIntegerRing59 K →+* LambdaResidueRing59 K :=
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K))
  have hqu : q (uR : LambdaIntegerRing59 K) = 1 := by
    have hzero : q ((uR : LambdaIntegerRing59 K) - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hu_sub_max
    rw [map_sub, map_one, sub_eq_zero] at hzero
    exact hzero
  have hqeps : q epsR = -1 := by
    have hzero : q (epsR + 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr heps_add_max
    rw [map_add, map_one] at hzero
    exact eq_neg_of_add_eq_zero_left hzero
  have hqRam := congrArg q hramIntegral
  rw [map_mul, map_pow, hqu, hqeps, one_pow] at hqRam
  change q (ramificationQuotientIntegral59 K) = -1
  simpa only [mul_neg, mul_one, neg_neg] using congrArg Neg.neg hqRam

/-- The inverse of the selected primitive root, as an element of the local
integer ring. -/
def primitiveRootInverseIntegral59 : LambdaIntegerRing59 K :=
  ⟨(lambdaLocalPrimitiveRoot59 K)⁻¹, by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      map_inv₀, primitiveRoot59_valuation, inv_one]⟩

theorem primitiveRootInverseIntegral59_residue_eq_one :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K))
        (primitiveRootInverseIntegral59 K) =
      (1 : LambdaResidueRing59 K) := by
  change Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K))
        (primitiveRootInverseIntegral59 K) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K)) 1
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [mem_lambdaMaximalIdeal59_iff]
  change Valued.v ((lambdaLocalPrimitiveRoot59 K)⁻¹ - 1) < 1
  have hzeta : lambdaLocalPrimitiveRoot59 K ≠ 0 :=
    (lambdaLocalPrimitiveRoot59_isPrimitive K).ne_zero (by norm_num)
  have hid : (lambdaLocalPrimitiveRoot59 K)⁻¹ - 1 =
      -(canonicalLambda59 K * (lambdaLocalPrimitiveRoot59 K)⁻¹) := by
    rw [canonicalLambda59]
    field_simp
    ring
  rw [hid, Valuation.map_neg, map_mul, map_inv₀,
    canonicalLambda59_valuation, primitiveRoot59_valuation, inv_one, mul_one]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

/-- Before reduction, the critical coefficient of the explicit correction
is the ramification quotient times the inverse primitive root. -/
theorem criticalCoefficientIntegral59_correction_eq :
    criticalCoefficientIntegral59 K (correctionInU59 K) =
      ramificationQuotientIntegral59 K * primitiveRootInverseIntegral59 K := by
  apply Subtype.ext
  change
    (primitiveRootNormCorrection59 K - 1) / canonicalLambda59 K ^ 59 =
      ((59 : LambdaField59 K) / canonicalLambda59 K ^ 58) *
        (lambdaLocalPrimitiveRoot59 K)⁻¹
  rw [primitiveRootNormCorrection59_eq]
  have hzeta : lambdaLocalPrimitiveRoot59 K ≠ 0 :=
    (lambdaLocalPrimitiveRoot59_isPrimitive K).ne_zero (by norm_num)
  field_simp [canonicalLambda59_ne_zero K, hzeta]
  ring

theorem criticalCoefficient59_mul (u v : U59 K) :
    criticalCoefficient59 K (u * v) =
      criticalCoefficient59 K u + criticalCoefficient59 K v := by
  change
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K))
        (criticalCoefficientIntegral59 K (u * v)) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K))
        (criticalCoefficientIntegral59 K u) +
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K))
        (criticalCoefficientIntegral59 K v)
  rw [← map_add]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [mem_lambdaMaximalIdeal59_iff]
  change Valued.v
      ((((((u * v : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) /
          canonicalLambda59 K ^ 59) -
        (((((u : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) /
            canonicalLambda59 K ^ 59 +
          ((((v : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) /
            canonicalLambda59 K ^ 59)) < 1
  have hid :
      ((((((u * v : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) /
          canonicalLambda59 K ^ 59) -
        (((((u : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) /
            canonicalLambda59 K ^ 59 +
          ((((v : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) /
            canonicalLambda59 K ^ 59)) =
        (((((u : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) *
          ((((v : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1)) /
            canonicalLambda59 K ^ 59 := by
    change
      (((((u : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) *
          (((v : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) /
            canonicalLambda59 K ^ 59) -
        (((((u : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) /
            canonicalLambda59 K ^ 59 +
          ((((v : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) /
            canonicalLambda59 K ^ 59) = _
    field_simp [canonicalLambda59_ne_zero K]
    ring
  rw [hid, div_eq_mul_inv, map_mul, map_mul, map_inv₀, map_pow,
    canonicalLambda59_valuation]
  have hu := u.property
  have hv := v.property
  rw [mem_lambdaOneUnits] at hu hv
  calc
    (Valued.v ((((u : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1)) *
          (Valued.v ((((v : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1)) *
          (WithZero.exp (-1 : ℤ) ^ 59)⁻¹
        ≤ WithZero.exp (-((59 : ℕ) : ℤ)) *
            WithZero.exp (-((59 : ℕ) : ℤ)) *
            (WithZero.exp (-1 : ℤ) ^ 59)⁻¹ := by
          gcongr
    _ = WithZero.exp (-59 : ℤ) := by
          norm_num [← WithZero.exp_nsmul]
    _ < 1 := by
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
          norm_num

/-- The first nonzero lambda-adic coefficient, with multiplication of
principal units read as addition in the residue ring. -/
def criticalCoefficientHom59 :
    U59 K →* Multiplicative (LambdaResidueRing59 K) where
  toFun u := Multiplicative.ofAdd (criticalCoefficient59 K u)
  map_one' := by
    change criticalCoefficient59 K 1 = 0
    rw [criticalCoefficient59, Ideal.Quotient.eq_zero_iff_mem,
      mem_lambdaMaximalIdeal59_iff]
    change Valued.v
      (((((1 : (U59 K)) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) /
        canonicalLambda59 K ^ 59) < 1
    simp
  map_mul' u v := by
    change criticalCoefficient59 K (u * v) =
      criticalCoefficient59 K u + criticalCoefficient59 K v
    exact criticalCoefficient59_mul K u v

theorem valuation_lt_depth59_iff_le_depth60
    (x : ℤᵐ⁰) :
    x < WithZero.exp (-59 : ℤ) ↔
      x ≤ WithZero.exp (-60 : ℤ) := by
  have h := WithZero.lt_mul_exp_iff_le
      (x := x) (y := WithZero.exp (-60 : ℤ))
      (WithZero.exp_ne_zero : WithZero.exp (-60 : ℤ) ≠ 0)
  rw [← WithZero.exp_add] at h
  have hsum : (-60 : ℤ) + 1 = -59 := by norm_num
  rw [hsum] at h
  exact h

theorem criticalCoefficient59_eq_zero_iff (u : U59 K) :
    criticalCoefficient59 K u = 0 ↔
      ((u : (LambdaField59 K)ˣ) ∈ U60 K) := by
  rw [criticalCoefficient59, Ideal.Quotient.eq_zero_iff_mem,
    mem_lambdaMaximalIdeal59_iff]
  change
    Valued.v
        (((((u : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) /
          canonicalLambda59 K ^ 59) < 1 ↔
      Valued.v
        ((((u : U59 K) : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) ≤
          WithZero.exp (-((60 : ℕ) : ℤ))
  rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow,
    canonicalLambda59_valuation]
  have hpos : 0 < WithZero.exp (-59 : ℤ) := WithZero.exp_pos
  rw [show WithZero.exp (-1 : ℤ) ^ 59 =
      WithZero.exp (-59 : ℤ) by
        norm_num [← WithZero.exp_nsmul]]
  rw [(mul_inv_lt_iff₀ hpos)]
  simp only [one_mul, valuation_lt_depth59_iff_le_depth60]
  norm_num

theorem criticalCoefficientHom59_ker :
    (criticalCoefficientHom59 K).ker = U60InU59 K := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change criticalCoefficient59 K u = 0 ↔
    ((u : (LambdaField59 K)ˣ) ∈ U60 K)
  exact criticalCoefficient59_eq_zero_iff K u

theorem U60InU59_le_criticalCoefficientHom59_ker :
    U60InU59 K ≤ (criticalCoefficientHom59 K).ker := by
  rw [criticalCoefficientHom59_ker]

/-- The canonical first-coefficient readout on the critical quotient. -/
def criticalLayerReadout59 :
    CriticalUnitLayer59 K →* Multiplicative (LambdaResidueRing59 K) :=
  QuotientGroup.lift (U60InU59 K) (criticalCoefficientHom59 K)
    (U60InU59_le_criticalCoefficientHom59_ker K)

@[simp]
theorem criticalLayerReadout59_mk (u : U59 K) :
    criticalLayerReadout59 K (QuotientGroup.mk u) =
      criticalCoefficientHom59 K u :=
  QuotientGroup.lift_mk' _ _ u

theorem criticalLayerReadout59_injective :
    Function.Injective (criticalLayerReadout59 K) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [criticalLayerReadout59, QuotientGroup.ker_lift,
    criticalCoefficientHom59_ker]
  exact QuotientGroup.map_mk'_self (U60InU59 K)

/-- The raw residue scalar carried by the explicit norm correction. -/
def correctionCoefficient59 : LambdaResidueRing59 K :=
  criticalCoefficient59 K (correctionInU59 K)

/-- In the canonical unscaled coordinate, the explicit correction carries
the classical Dwork scalar `-1`. -/
theorem correctionCoefficient59_eq_neg_one :
    correctionCoefficient59 K = (-1 : LambdaResidueRing59 K) := by
  rw [correctionCoefficient59, criticalCoefficient59,
    criticalCoefficientIntegral59_correction_eq, map_mul,
    ramificationQuotientIntegral59_residue_eq_neg_one,
    primitiveRootInverseIntegral59_residue_eq_one, mul_one]

theorem correctionCoefficient59_ne_zero :
    correctionCoefficient59 K ≠ 0 := by
  intro hzero
  have hmem := (criticalCoefficient59_eq_zero_iff K
    (correctionInU59 K)).mp hzero
  exact correctionFieldUnit59_not_mem_U60 K hmem

@[simp]
theorem criticalLayerReadout59_correctionClass :
    criticalLayerReadout59 K (correctionClass59 K) =
      Multiplicative.ofAdd (correctionCoefficient59 K) := by
  rfl

/-- Multiplication by a residue scalar, viewed as a homomorphism of the
underlying additive group. -/
def residueScale59 (a : LambdaResidueRing59 K) :
    Multiplicative (LambdaResidueRing59 K) →*
      Multiplicative (LambdaResidueRing59 K) where
  toFun x := Multiplicative.ofAdd (a * Multiplicative.toAdd x)
  map_one' := by simp
  map_mul' x y := by
    change a * (Multiplicative.toAdd x + Multiplicative.toAdd y) =
      a * Multiplicative.toAdd x + a * Multiplicative.toAdd y
    exact mul_add _ _ _

theorem residueScale59_injective {a : LambdaResidueRing59 K}
    (ha : a ≠ 0) : Function.Injective (residueScale59 K a) := by
  intro x y hxy
  apply Multiplicative.toAdd.injective
  change a * Multiplicative.toAdd x = a * Multiplicative.toAdd y at hxy
  exact mul_left_cancel₀ ha hxy

/-- The same readout, canonically rescaled by the inverse of the correction
coefficient.  It sends that selected nonzero class to scalar `1`. -/
def normalizedCriticalLayerReadout59 :
    CriticalUnitLayer59 K →* Multiplicative (LambdaResidueRing59 K) :=
  (residueScale59 K (correctionCoefficient59 K)⁻¹).comp
    (criticalLayerReadout59 K)

theorem normalizedCriticalLayerReadout59_injective :
    Function.Injective (normalizedCriticalLayerReadout59 K) :=
  (residueScale59_injective K
    (inv_ne_zero (correctionCoefficient59_ne_zero K))).comp
      (criticalLayerReadout59_injective K)

@[simp]
theorem normalizedCriticalLayerReadout59_correctionClass :
    normalizedCriticalLayerReadout59 K (correctionClass59 K) =
      Multiplicative.ofAdd (1 : LambdaResidueRing59 K) := by
  change Multiplicative.ofAdd
      ((correctionCoefficient59 K)⁻¹ * correctionCoefficient59 K) =
    Multiplicative.ofAdd (1 : LambdaResidueRing59 K)
  rw [inv_mul_cancel₀ (correctionCoefficient59_ne_zero K)]

/-! ## Every residue scalar occurs -/

def criticalUnitValueOfIntegral59 (a : LambdaIntegerRing59 K) :
    LambdaField59 K :=
  1 + (a : LambdaField59 K) * canonicalLambda59 K ^ 59

theorem criticalUnitPerturbationOfIntegral59_valuation_le
    (a : LambdaIntegerRing59 K) :
    Valued.v ((a : LambdaField59 K) * canonicalLambda59 K ^ 59) ≤
      WithZero.exp (-59 : ℤ) := by
  rw [map_mul, map_pow, canonicalLambda59_valuation]
  have ha : Valued.v (a : LambdaField59 K) ≤ 1 := a.property
  calc
    Valued.v (a : LambdaField59 K) * WithZero.exp (-1 : ℤ) ^ 59 ≤
        1 * WithZero.exp (-1 : ℤ) ^ 59 := by gcongr
    _ = WithZero.exp (-59 : ℤ) := by
      norm_num [← WithZero.exp_nsmul]

theorem criticalUnitValueOfIntegral59_valuation
    (a : LambdaIntegerRing59 K) :
    Valued.v (criticalUnitValueOfIntegral59 K a) = 1 := by
  apply (Valued.v : Valuation (LambdaField59 K) ℤᵐ⁰).map_one_add_of_lt
  exact (criticalUnitPerturbationOfIntegral59_valuation_le K a).trans_lt (by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num)

theorem criticalUnitValueOfIntegral59_ne_zero
    (a : LambdaIntegerRing59 K) :
    criticalUnitValueOfIntegral59 K a ≠ 0 := by
  intro hzero
  have hval := criticalUnitValueOfIntegral59_valuation K a
  rw [hzero, map_zero] at hval
  exact zero_ne_one hval

def criticalUnitOfIntegral59 (a : LambdaIntegerRing59 K) : U59 K :=
  ⟨Units.mk0 (criticalUnitValueOfIntegral59 K a)
      (criticalUnitValueOfIntegral59_ne_zero K a), by
    rw [mem_lambdaOneUnits]
    change Valued.v (criticalUnitValueOfIntegral59 K a - 1) ≤
      WithZero.exp (-((59 : ℕ) : ℤ))
    rw [criticalUnitValueOfIntegral59]
    rw [add_sub_cancel_left]
    exact criticalUnitPerturbationOfIntegral59_valuation_le K a⟩

theorem criticalCoefficientIntegral59_of_integral
    (a : LambdaIntegerRing59 K) :
    criticalCoefficientIntegral59 K (criticalUnitOfIntegral59 K a) = a := by
  apply Subtype.ext
  change
    ((criticalUnitValueOfIntegral59 K a - 1) /
      canonicalLambda59 K ^ 59) = (a : LambdaField59 K)
  rw [criticalUnitValueOfIntegral59]
  rw [add_sub_cancel_left]
  field_simp [canonicalLambda59_ne_zero K]

theorem criticalCoefficient59_of_integral
    (a : LambdaIntegerRing59 K) :
    criticalCoefficient59 K (criticalUnitOfIntegral59 K a) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (LambdaIntegerRing59 K)) a := by
  rw [criticalCoefficient59, criticalCoefficientIntegral59_of_integral]

theorem criticalCoefficientHom59_surjective :
    Function.Surjective (criticalCoefficientHom59 K) := by
  intro x
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (Multiplicative.toAdd x)
  refine ⟨criticalUnitOfIntegral59 K a, ?_⟩
  apply Multiplicative.toAdd.injective
  change criticalCoefficient59 K (criticalUnitOfIntegral59 K a) =
    Multiplicative.toAdd x
  rw [criticalCoefficient59_of_integral, ha]

theorem criticalLayerReadout59_surjective :
    Function.Surjective (criticalLayerReadout59 K) := by
  intro x
  obtain ⟨u, hu⟩ := criticalCoefficientHom59_surjective K x
  exact ⟨QuotientGroup.mk u, by
    rw [criticalLayerReadout59_mk, hu]⟩

/-- The critical one-unit quotient is exactly the additive group of the
lambda residue field, not merely a nonzero subgroup of it. -/
noncomputable def criticalLayerResidueEquiv59 :
    CriticalUnitLayer59 K ≃* Multiplicative (LambdaResidueRing59 K) :=
  MulEquiv.ofBijective (criticalLayerReadout59 K)
    ⟨criticalLayerReadout59_injective K, criticalLayerReadout59_surjective K⟩

/-- The requested prime-field presentation of the critical layer. -/
noncomputable def criticalLayerZModEquiv59 :
    CriticalUnitLayer59 K ≃* Multiplicative (ZMod 59) :=
  (criticalLayerResidueEquiv59 K).trans
    (zmodEquivLambdaResidue59 K).symm.toAddEquiv.toMultiplicative

end Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59
