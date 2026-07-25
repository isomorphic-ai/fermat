import Fermat.SixHundredSeven.VandiverDiagonalDerivative607
import Fermat.SixHundredSeven.VandiverDiagonalUnits607

/-!
# Vandiver's integral unit polynomials at exponent 607

This file identifies the two incarnations of the diagonal units used in
Vandiver's Lemma II.

For a positive integer `s`, put

`epsilon_s(W) = W^(201*s) * (1 + W^s + ... + W^(812*s))`.

At `W = zeta`, these are the literal normalized circular units used in
`VandiverDiagonalUnits607`.  After the formal substitution `W = exp V`,
they are the normalized geometric exponential series used in
`VandiverDiagonalDerivative607`.
-/

open scoped BigOperators NumberField

namespace Fermat.SixHundredSeven.VandiverPolynomialUnits

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.SixHundredSeven.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

set_option maxRecDepth 100000

/-- Formal substitution of `exp V` into an integer polynomial. -/
def polynomialExp607 (P : Polynomial ℤ) : PowerSeries ℚ :=
  Polynomial.eval₂ (algebraMap ℤ (PowerSeries ℚ))
    (PowerSeries.exp ℚ) P

/-- Vandiver's basic integral polynomial
`W^(201*s) * (1 + W^s + ... + W^(812*s))`. -/
def basicVandiverPolynomial607 (s : ℕ) : Polynomial ℤ :=
  Polynomial.X ^ (201 * s) *
    ∑ j ∈ Finset.range 813, Polynomial.X ^ (s * j)

/-- Substitution `W = exp V` turns the basic integral polynomial into
the normalized geometric exponential used in the derivative calculation. -/
theorem polynomialExp607_basicVandiverPolynomial607 (s : ℕ) :
    polynomialExp607 (basicVandiverPolynomial607 s) =
      normalizedGeomExp 813 201 s := by
  rw [polynomialExp607, basicVandiverPolynomial607, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_finsetSum]
  simp_rw [Polynomial.eval₂_pow, Polynomial.eval₂_X]
  rw [normalizedGeomExp]
  congr 1
  rw [geomExp, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_pow, ← PowerSeries.exp_pow_eq_rescale_exp (A := ℚ) s,
    ← pow_mul]

variable {K : Type*} [Field K]

/-- At the integral lift of `zeta`, the basic polynomial is the actual
basic Vandiver unit. -/
theorem eval₂_basicVandiverPolynomial607 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607)
    (j : VandiverFactorIndex607) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (basicVandiverPolynomial607 (conjugateExponent607 j)) =
      (basicVandiverUnit607 hzeta j : 𝓞 K) := by
  rw [basicVandiverUnit607,
    Fermat.Irregular.CircularUnitFamily.normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [basicVandiverPolynomial607, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_finsetSum]
  congr 1
  all_goals simp only [← pow_mul]
  all_goals ring_nf

/-- Vandiver's positive integral polynomial representing the `i`th
diagonal unit. -/
def diagonalVandiverPolynomial607
    (i : SourceIndex 607) : Polynomial ℤ :=
  ∏ j : VandiverFactorIndex607,
    basicVandiverPolynomial607 (conjugateExponent607 j) ^
      diagonalWeight607 i j

/-- The exponential substitution of the actual diagonal polynomial is
the formal diagonal series used in the derivative theorem. -/
theorem polynomialExp607_diagonalVandiverPolynomial607
    (i : SourceIndex 607) :
    polynomialExp607 (diagonalVandiverPolynomial607 i) =
      Fermat.SixHundredSeven.VandiverDiagonalDerivative.integralDiagonalSeries607 i := by
  rw [diagonalVandiverPolynomial607, polynomialExp607,
    Polynomial.eval₂_finsetProd]
  simp_rw [Polynomial.eval₂_pow]
  rw [Fermat.SixHundredSeven.VandiverDiagonalDerivative.integralDiagonalSeries607,
    integralDiagonalExp]
  norm_num
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [dif_pos hj]
  simp only [integralDiagonalFactor, diagonalWeight607,
    conjugateExponent607, sourceNumber]
  change
    (polynomialExp607 (basicVandiverPolynomial607 (813 ^ j))) ^
          integralDiagonalWeight 607 813 (i.val + 1) j =
      normalizedGeomExp 813 201 (813 ^ j) ^
          integralDiagonalWeight 607 813 (i.val + 1) j
  rw [polynomialExp607_basicVandiverPolynomial607]

variable [NumberField K] [IsCyclotomicExtension {607} ℚ K]
  [NumberField.IsCMField K]

omit [NumberField K] [IsCyclotomicExtension {607} ℚ K]
    [NumberField.IsCMField K] in
/-- Evaluation at the chosen primitive root gives the literal ambient
diagonal unit constructed in `VandiverDiagonalUnits607`. -/
theorem eval₂_diagonalVandiverPolynomial607 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607) (i : SourceIndex 607) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (diagonalVandiverPolynomial607 i) =
      (diagonalVandiverUnit607 hzeta i : 𝓞 K) := by
  rw [diagonalVandiverPolynomial607, Polynomial.eval₂_finsetProd,
    diagonalVandiverUnit607]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval₂_pow]
  congr 1
  exact eval₂_basicVandiverPolynomial607 hzeta j

/-! ## Polynomials attached to an arbitrary integer exponent relation -/

/-- The positive polynomial attached to natural exponents `b`.  The outer
factor `606 = 607 - 1` is exactly Vandiver's factor in equation (3b). -/
def positiveRelationPolynomial607
    (b : SourceIndex 607 → ℕ) : Polynomial ℤ :=
  ∏ i, diagonalVandiverPolynomial607 i ^ (606 * b i)

/-- Exponential substitution commutes with the positive relation product. -/
theorem polynomialExp607_positiveRelationPolynomial607
    (b : SourceIndex 607 → ℕ) :
    polynomialExp607 (positiveRelationPolynomial607 b) =
      ∏ i,
        Fermat.SixHundredSeven.VandiverDiagonalDerivative.integralDiagonalSeries607 i ^
          (606 * b i) := by
  rw [positiveRelationPolynomial607, polynomialExp607,
    Polynomial.eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow]
  congr 1
  exact polynomialExp607_diagonalVandiverPolynomial607 i

/-- Every diagonal series has nonzero constant coefficient. -/
theorem constantCoeff_integralDiagonalSeries607_ne_zero
    (i : SourceIndex 607) :
    PowerSeries.constantCoeff
      (Fermat.SixHundredSeven.VandiverDiagonalDerivative.integralDiagonalSeries607 i) ≠
        0 := by
  rw [Fermat.SixHundredSeven.VandiverDiagonalDerivative.integralDiagonalSeries607,
    integralDiagonalExp]
  simp only [map_prod, constantCoeff_integralDiagonalFactor]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact pow_ne_zero _ (by norm_num)

/-- The logarithmic derivative of a positive polynomial product is the
expected natural-exponent sum. -/
theorem logarithmicDerivative_positiveRelationPolynomial607
    (b : SourceIndex 607 → ℕ) :
    logarithmicDerivative
        (polynomialExp607 (positiveRelationPolynomial607 b)) =
      ∑ i, PowerSeries.C ((606 * b i : ℕ) : ℚ) *
        logarithmicDerivative
          (Fermat.SixHundredSeven.VandiverDiagonalDerivative.integralDiagonalSeries607 i) := by
  rw [polynomialExp607_positiveRelationPolynomial607 b]
  rw [logarithmicDerivative_prod]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [logarithmicDerivative_pow]
    exact constantCoeff_integralDiagonalSeries607_ne_zero i
  · intro i hi
    apply constantCoeff_pow_ne_zero
    exact constantCoeff_integralDiagonalSeries607_ne_zero i

/-- High derivatives of the preceding identity, in the exact normalization
used by `relationDerivative607`. -/
theorem formalDerivativeAtZero_positiveRelationPolynomial607
    (b : SourceIndex 607 → ℕ) (k : SourceIndex 607) :
    formalDerivativeAtZero
      (Fermat.SixHundredSeven.VandiverDiagonalDerivative.sourceDerivativeOrder607 k)
      (logarithmicDerivative
        (polynomialExp607 (positiveRelationPolynomial607 b))) =
      ∑ i, ((606 * b i : ℕ) : ℚ) *
        formalDerivativeAtZero
          (Fermat.SixHundredSeven.VandiverDiagonalDerivative.sourceDerivativeOrder607 k)
          (logarithmicDerivative
            (Fermat.SixHundredSeven.VandiverDiagonalDerivative.integralDiagonalSeries607 i)) := by
  rw [logarithmicDerivative_positiveRelationPolynomial607 b,
    formalDerivativeAtZero_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [formalDerivativeAtZero_C_mul]

/-- Clearing negative exponents does not change the source derivative:
the integer relation derivative is the logarithmic derivative of the
positive numerator minus that of the positive denominator. -/
theorem relationDerivative607_eq_positive_sub_negative
    (a : SourceIndex 607 → ℤ) (k : SourceIndex 607) :
    Fermat.SixHundredSeven.VandiverDiagonalDerivative.relationDerivative607 a k =
      formalDerivativeAtZero
        (Fermat.SixHundredSeven.VandiverDiagonalDerivative.sourceDerivativeOrder607 k)
        (logarithmicDerivative
          (polynomialExp607
            (positiveRelationPolynomial607 (fun i ↦ (a i).toNat)))) -
      formalDerivativeAtZero
        (Fermat.SixHundredSeven.VandiverDiagonalDerivative.sourceDerivativeOrder607 k)
        (logarithmicDerivative
          (polynomialExp607
            (positiveRelationPolynomial607
              (fun i ↦ (-a i).toNat)))) := by
  rw [formalDerivativeAtZero_positiveRelationPolynomial607,
    formalDerivativeAtZero_positiveRelationPolynomial607]
  rw [Fermat.SixHundredSeven.VandiverDiagonalDerivative.relationDerivative607,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  have haQ :
      ((a i).toNat : ℚ) - ((-a i).toNat : ℚ) = (a i : ℚ) := by
    exact_mod_cast Int.toNat_sub_toNat_neg (a i)
  rw [← haQ]
  ring

/-- The positive and negative parts of an integer exponent recombine in
any commutative group. -/
theorem zpow_mul_pow_negToNat_eq_pow_toNat
    {G : Type*} [CommGroup G] (x : G) (a : ℤ) :
    x ^ a * x ^ (-a).toNat = x ^ a.toNat := by
  rw [← zpow_natCast x a.toNat, ← zpow_natCast x (-a).toNat,
    ← zpow_add]
  congr 1
  exact (eq_sub_iff_add_eq).mp (Int.toNat_sub_toNat_neg a).symm

/-- A Laurent exponent relation becomes a denominator-cleared positive
relation. -/
theorem positive_relation_of_zpow_relation
    {G : Type*} [CommGroup G] {u : G}
    (E : SourceIndex 607 → G) (t : ℕ)
    (a : SourceIndex 607 → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (∏ i, E i ^ (a i).toNat) =
      u ^ t * ∏ i, E i ^ (-a i).toNat := by
  rw [hrel, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact (zpow_mul_pow_negToNat_eq_pow_toNat (E i) (a i)).symm

/-- The ambient unit represented by the unscaled positive exponent
product.  Its 606th power is the value of
`positiveRelationPolynomial607`. -/
def positiveRelationUnit607 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607)
    (b : SourceIndex 607 → ℕ) : (𝓞 K)ˣ :=
  ∏ i, diagonalVandiverUnit607 hzeta i ^ b i

omit [NumberField K] [IsCyclotomicExtension {607} ℚ K]
    [NumberField.IsCMField K] in
/-- Evaluation of a positive relation polynomial is the 606th power of
its corresponding unit product. -/
theorem eval₂_positiveRelationPolynomial607 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607)
    (b : SourceIndex 607 → ℕ) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial607 b) =
      (positiveRelationUnit607 hzeta b ^ 606 : 𝓞 K) := by
  rw [positiveRelationPolynomial607, Polynomial.eval₂_finsetProd,
    positiveRelationUnit607, Units.coe_prod]
  simp_rw [Units.val_pow_eq_pow_val]
  rw [← Finset.prod_pow Finset.univ 606
    (fun i ↦ (diagonalVandiverUnit607 hzeta i : 𝓞 K) ^ b i)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow, eval₂_diagonalVandiverPolynomial607,
    ← pow_mul]
  congr 1
  omega

omit [NumberField K] [IsCyclotomicExtension {607} ℚ K]
    [NumberField.IsCMField K] in
/-- An actual unit relation gives the exact denominator-cleared evaluation
identity to which the cyclotomic polynomial remainder theorem is applied. -/
theorem eval₂_positive_relation_of_relation {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 607)
    (u : (𝓞 K)ˣ) (t : ℕ) (a : SourceIndex 607 → ℤ)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit607 hzeta i ^ a i) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial607 (fun i ↦ (a i).toNat)) =
      (u : 𝓞 K) ^ (606 * t) *
        Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
          (positiveRelationPolynomial607 (fun i ↦ (-a i).toNat)) := by
  rw [eval₂_positiveRelationPolynomial607,
    eval₂_positiveRelationPolynomial607]
  have hpos := positive_relation_of_zpow_relation
    (E := diagonalVandiverUnit607 hzeta) t a hrel
  have hpow := congrArg (fun x : (𝓞 K)ˣ ↦ x ^ 606) hpos
  have hval := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hpow
  simpa only [positiveRelationUnit607, Units.val_pow_eq_pow_val,
    Units.val_mul, mul_pow, ← pow_mul, Nat.mul_comm] using hval

end

end Fermat.SixHundredSeven.VandiverPolynomialUnits
