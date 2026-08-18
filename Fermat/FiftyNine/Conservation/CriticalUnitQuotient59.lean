/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The critical one-unit quotient at 59

This module defines the genuine positive lambda-adic one-unit filtration
inside the unit group of the concrete local field.  The correction isolated
by `TwistedLambdaNormCorrection59` lies in `U_59` but not `U_60`, and hence
defines a nonzero class in `U_59 / U_60`.

It also maps actual norms from the twisted Kummer extension into this
critical quotient.  Excluding the correction class from that image is
exposed as the precise remaining sufficient arithmetic statement.  No
Artin--Hasse value, norm-filtration hyperplane, provider, or assumption is
introduced here.
-/
import Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
import KummerCriterion.Reflection.Local.DeltaAction
import Mathlib.GroupTheory.QuotientGroup.Basic

open scoped NumberField WithZero

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.CriticalUnitQuotient59

open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- Units congruent to one to lambda-adic depth at least `n`.  The positive
depth hypothesis is what ensures that this condition is closed under
inversion inside the ambient field-unit group. -/
def lambdaOneUnits (n : ℕ) (hn : 0 < n) :
    Subgroup (LambdaField59 K)ˣ where
  carrier := {u | Valued.v ((u : LambdaField59 K) - 1) ≤
    WithZero.exp (-(n : ℤ))}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    have hbound : WithZero.exp (-(n : ℤ)) < (1 : ℤᵐ⁰) := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have huval : Valued.v (u : LambdaField59 K) = 1 := by
      have hlt : Valued.v ((u : LambdaField59 K) - 1) < 1 :=
        hu.trans_lt hbound
      have hone :=
        (Valued.v : Valuation (LambdaField59 K) ℤᵐ⁰).map_one_add_of_lt hlt
      simpa using hone
    have hidentity :
        ((u * v : (LambdaField59 K)ˣ) : LambdaField59 K) - 1 =
          (u : LambdaField59 K) * ((v : LambdaField59 K) - 1) +
            ((u : LambdaField59 K) - 1) := by
      change (u : LambdaField59 K) * (v : LambdaField59 K) - 1 = _
      ring
    change Valued.v
      (((u * v : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) ≤ _
    rw [hidentity]
    apply (Valued.v : Valuation (LambdaField59 K) ℤᵐ⁰).map_add_le
    · rw [map_mul, huval, one_mul]
      exact hv
    · exact hu
  inv_mem' := by
    intro u hu
    have hbound : WithZero.exp (-(n : ℤ)) < (1 : ℤᵐ⁰) := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have huval : Valued.v (u : LambdaField59 K) = 1 := by
      have hlt : Valued.v ((u : LambdaField59 K) - 1) < 1 :=
        hu.trans_lt hbound
      have hone :=
        (Valued.v : Valuation (LambdaField59 K) ℤᵐ⁰).map_one_add_of_lt hlt
      simpa using hone
    have hidentity :
        ((u⁻¹ : (LambdaField59 K)ˣ) : LambdaField59 K) - 1 =
          -((u⁻¹ : (LambdaField59 K)ˣ) : LambdaField59 K) *
            ((u : LambdaField59 K) - 1) := by
      rw [Units.val_inv_eq_inv_val]
      change (u : LambdaField59 K)⁻¹ - 1 =
        -(u : LambdaField59 K)⁻¹ * ((u : LambdaField59 K) - 1)
      field_simp
      ring
    change Valued.v
      (((u⁻¹ : (LambdaField59 K)ˣ) : LambdaField59 K) - 1) ≤ _
    rw [hidentity, map_mul, Valuation.map_neg, Units.val_inv_eq_inv_val,
      map_inv₀, huval,
      inv_one, one_mul]
    exact hu

@[simp]
theorem mem_lambdaOneUnits {n : ℕ} {hn : 0 < n}
    {u : (LambdaField59 K)ˣ} :
    u ∈ lambdaOneUnits K n hn ↔
      Valued.v ((u : LambdaField59 K) - 1) ≤
        WithZero.exp (-(n : ℤ)) :=
  Iff.rfl

/-- Deeper positive one-unit levels are contained in shallower levels. -/
theorem lambdaOneUnits_mono {m n : ℕ} {hm : 0 < m} {hn : 0 < n}
    (h : m ≤ n) :
    lambdaOneUnits K n hn ≤ lambdaOneUnits K m hm := by
  intro u hu
  rw [mem_lambdaOneUnits] at hu ⊢
  exact hu.trans (by
    rw [WithZero.exp_le_exp]
    omega)

abbrev U59 : Subgroup (LambdaField59 K)ˣ :=
  lambdaOneUnits K 59 (by norm_num)

abbrev U60 : Subgroup (LambdaField59 K)ˣ :=
  lambdaOneUnits K 60 (by norm_num)

theorem U60_le_U59 : U60 K ≤ U59 K :=
  lambdaOneUnits_mono K (by norm_num)

/-- The correction viewed as an actual unit of the local field. -/
def correctionFieldUnit59 : (LambdaField59 K)ˣ :=
  Units.mk0 (primitiveRootNormCorrection59 K)
    (primitiveRootNormCorrection59_ne_zero K)

@[simp]
theorem correctionFieldUnit59_val :
    (correctionFieldUnit59 K : LambdaField59 K) =
      primitiveRootNormCorrection59 K :=
  rfl

theorem correctionFieldUnit59_mem_U59 :
    correctionFieldUnit59 K ∈ U59 K := by
  rw [mem_lambdaOneUnits, correctionFieldUnit59_val,
    primitiveRootNormCorrection59_sub_one_valuation]
  norm_num

theorem correctionFieldUnit59_not_mem_U60 :
    correctionFieldUnit59 K ∉ U60 K := by
  intro h
  rw [mem_lambdaOneUnits, correctionFieldUnit59_val,
    primitiveRootNormCorrection59_sub_one_valuation] at h
  rw [WithZero.exp_le_exp] at h
  norm_num at h

/-- The depth-60 subgroup, now seated inside the depth-59 group. -/
abbrev U60InU59 : Subgroup (U59 K) :=
  (U60 K).subgroupOf (U59 K)

/-- The first critical one-unit quotient for the twisted-lambda correction. -/
abbrev CriticalUnitLayer59 := (U59 K) ⧸ U60InU59 K

/-- The correction as an element of `U_59`. -/
def correctionInU59 : U59 K :=
  ⟨correctionFieldUnit59 K, correctionFieldUnit59_mem_U59 K⟩

/-- Its class in `U_59 / U_60`. -/
def correctionClass59 : CriticalUnitLayer59 K :=
  QuotientGroup.mk (correctionInU59 K)

theorem correctionClass59_ne_one : correctionClass59 K ≠ 1 := by
  intro hzero
  have hmem : correctionInU59 K ∈ U60InU59 K :=
    (QuotientGroup.eq_one_iff _).mp hzero
  exact correctionFieldUnit59_not_mem_U60 K
    ((Subgroup.mem_subgroupOf).mp hmem)

/-- The critical layer is genuinely nontrivial, witnessed by the correction
class itself. -/
noncomputable instance criticalUnitLayer59Nontrivial :
    Nontrivial (CriticalUnitLayer59 K) :=
  ⟨⟨correctionClass59 K, 1, correctionClass59_ne_one K⟩⟩

/-! ## The actual norm image on the critical quotient -/

/-- The field norm, restricted to multiplicative units.  No local
reciprocity or norm-filtration theorem enters this definition. -/
def twistedLambdaNormUnits59 :
    (twistedLambdaKummerExtension59 K)ˣ →*
      (LambdaField59 K)ˣ :=
  Units.map (Algebra.norm (LambdaField59 K))

/-- Actual field norms which happen to lie in `U_59`, seated as a subgroup
of `U_59`. -/
def normUnitsInU59 : Subgroup (U59 K) :=
  (twistedLambdaNormUnits59 K).range.subgroupOf (U59 K)

/-- The image in `U_59/U_60` of all actual field norms lying in `U_59`.
This is an image subgroup, not an asserted hyperplane. -/
def normImageCriticalUnitLayer59 : Subgroup (CriticalUnitLayer59 K) :=
  (normUnitsInU59 K).map (QuotientGroup.mk' (U60InU59 K))

/-- A concrete norm witness for the correction places its critical class in
the actual quotient norm image. -/
theorem correctionClass59_mem_normImage_of_norm
    (gamma : twistedLambdaKummerExtension59 K)
    (hgamma : Algebra.norm (LambdaField59 K) gamma =
      primitiveRootNormCorrection59 K) :
    correctionClass59 K ∈ normImageCriticalUnitLayer59 K := by
  letI : Polynomial.IsSplittingField (LambdaField59 K)
      (twistedLambdaKummerExtension59 K)
      (Fermat.Conservation.KummerCyclicQuotient59.kummerPolynomial59
        (LambdaField59 K) (twistedLambda59 K)) :=
    Fermat.Conservation.KummerCyclicQuotient59.kummerExtension59_isSplittingField
      (LambdaField59 K) (twistedLambda59 K)
  letI : FiniteDimensional (LambdaField59 K)
      (twistedLambdaKummerExtension59 K) :=
    Polynomial.IsSplittingField.finiteDimensional
      (twistedLambdaKummerExtension59 K)
      (Fermat.Conservation.KummerCyclicQuotient59.kummerPolynomial59
        (LambdaField59 K) (twistedLambda59 K))
  have hgamma0 : gamma ≠ 0 := by
    apply (Algebra.norm_ne_zero_iff
      (R := LambdaField59 K)
      (S := twistedLambdaKummerExtension59 K)).mp
    rw [hgamma]
    exact primitiveRootNormCorrection59_ne_zero K
  let gammaUnit : (twistedLambdaKummerExtension59 K)ˣ :=
    Units.mk0 gamma hgamma0
  have hnormUnit :
      twistedLambdaNormUnits59 K gammaUnit = correctionFieldUnit59 K := by
    apply Units.ext
    exact hgamma
  have hnormMem : correctionInU59 K ∈ normUnitsInU59 K := by
    rw [normUnitsInU59, Subgroup.mem_subgroupOf]
    refine ⟨gammaUnit, ?_⟩
    exact hnormUnit
  refine ⟨correctionInU59 K, hnormMem, ?_⟩
  rfl

/-- Consequently, exclusion of the explicit nonzero critical class from the
actual norm image is sufficient to rule out a norm witness for the local
primitive root.  Proving the exclusion hypothesis is precisely the remaining
Artin--Hasse/norm-filtration theorem; it is deliberately not installed here. -/
theorem primitiveRoot_not_norm_of_correctionClass_not_mem_normImage
    (hexclusion : correctionClass59 K ∉ normImageCriticalUnitLayer59 K) :
    ¬ ∃ beta : twistedLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) beta =
        lambdaLocalPrimitiveRoot59 K := by
  rintro ⟨beta, hbeta⟩
  obtain ⟨gamma, hgamma⟩ :=
    exists_correction_norm_of_primitiveRoot_norm K beta hbeta
  exact hexclusion
    (correctionClass59_mem_normImage_of_norm K gamma hgamma)

end Fermat.FiftyNine.Conservation.CriticalUnitQuotient59
