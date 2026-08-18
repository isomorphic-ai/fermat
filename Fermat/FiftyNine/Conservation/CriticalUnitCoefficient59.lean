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

The explicit correction has a nonzero raw coefficient.  Scaling by its
inverse gives a canonical normalized meter on which the correction reads
`1`.  This is local algebra only: no reciprocity value, norm-filtration
hyperplane, provider, or assumption is introduced.  We deliberately retain
the intrinsic residue-field type; identifying it with `ZMod 59` additionally
requires a completion/global-residue comparison not present in the pinned
API.
-/
import Fermat.FiftyNine.Conservation.CriticalUnitQuotient59

open scoped NumberField WithZero

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59

open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
open Fermat.FiftyNine.Conservation.CriticalUnitQuotient59

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

theorem canonicalLambda59_ne_zero : canonicalLambda59 K ≠ 0 := by
  intro hzero
  have hval := canonicalLambda59_valuation K
  rw [hzero, map_zero] at hval
  exact WithZero.exp_ne_zero hval.symm

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

end Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59
