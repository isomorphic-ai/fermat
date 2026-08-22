import Fermat.Exponents.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative1381
import Fermat.Exponents.OneThousandThreeHundredEightyOne.VandiverDiagonalUnits1381

/-!
# Vandiver's integral unit polynomials at exponent 1381

This file identifies the two incarnations of the diagonal units used in
Vandiver's Lemma II.

For a positive integer `s`, put

`epsilon_s(W) = W^(1055*s) * (1 + W^s + ... + W^(652*s))`.

At `W = zeta`, these are the literal normalized circular units used in
`VandiverDiagonalUnits1381`.  After the formal substitution `W = exp V`,
they are the normalized geometric exponential series used in
`VandiverDiagonalDerivative1381`.
-/

open scoped BigOperators NumberField

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverPolynomialUnits

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

set_option maxRecDepth 100000

/-- Formal substitution of `exp V` into an integer polynomial. -/
def polynomialExp1381 (P : Polynomial ℤ) : PowerSeries ℚ :=
  Polynomial.eval₂ (algebraMap ℤ (PowerSeries ℚ))
    (PowerSeries.exp ℚ) P

/-- Vandiver's basic integral polynomial
`W^(1055*s) * (1 + W^s + ... + W^(652*s))`. -/
def basicVandiverPolynomial1381 (s : ℕ) : Polynomial ℤ :=
  Polynomial.X ^ (1055 * s) *
    ∑ j ∈ Finset.range 653, Polynomial.X ^ (s * j)

/-- Substitution `W = exp V` turns the basic integral polynomial into
the normalized geometric exponential used in the derivative calculation. -/
theorem polynomialExp1381_basicVandiverPolynomial1381 (s : ℕ) :
    polynomialExp1381 (basicVandiverPolynomial1381 s) =
      normalizedGeomExp 653 1055 s := by
  rw [polynomialExp1381, basicVandiverPolynomial1381, Polynomial.eval₂_mul,
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
theorem eval₂_basicVandiverPolynomial1381 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381)
    (j : VandiverFactorIndex1381) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (basicVandiverPolynomial1381 (conjugateExponent1381 j)) =
      (basicVandiverUnit1381 hzeta j : 𝓞 K) := by
  rw [basicVandiverUnit1381,
    Fermat.Irregular.CircularUnitFamily.normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [basicVandiverPolynomial1381, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_finsetSum]
  congr 1
  all_goals simp only [← pow_mul]
  all_goals ring_nf

/-- Vandiver's positive integral polynomial representing the `i`th
diagonal unit. -/
def diagonalVandiverPolynomial1381
    (i : SourceIndex 1381) : Polynomial ℤ :=
  ∏ j : VandiverFactorIndex1381,
    basicVandiverPolynomial1381 (conjugateExponent1381 j) ^
      diagonalWeight1381 i j

/-- The exponential substitution of the actual diagonal polynomial is
the formal diagonal series used in the derivative theorem. -/
theorem polynomialExp1381_diagonalVandiverPolynomial1381
    (i : SourceIndex 1381) :
    polynomialExp1381 (diagonalVandiverPolynomial1381 i) =
      Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative.integralDiagonalSeries1381 i := by
  rw [diagonalVandiverPolynomial1381, polynomialExp1381,
    Polynomial.eval₂_finsetProd]
  simp_rw [Polynomial.eval₂_pow]
  rw [Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative.integralDiagonalSeries1381,
    integralDiagonalExp]
  norm_num
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [dif_pos hj]
  simp only [integralDiagonalFactor, diagonalWeight1381,
    conjugateExponent1381, sourceNumber]
  change
    (polynomialExp1381 (basicVandiverPolynomial1381 (653 ^ j))) ^
          integralDiagonalWeight 1381 653 (i.val + 1) j =
      normalizedGeomExp 653 1055 (653 ^ j) ^
          integralDiagonalWeight 1381 653 (i.val + 1) j
  rw [polynomialExp1381_basicVandiverPolynomial1381]

variable [NumberField K] [IsCyclotomicExtension {1381} ℚ K]
  [NumberField.IsCMField K]

omit [NumberField K] [IsCyclotomicExtension {1381} ℚ K]
    [NumberField.IsCMField K] in
/-- Evaluation at the chosen primitive root gives the literal ambient
diagonal unit constructed in `VandiverDiagonalUnits1381`. -/
theorem eval₂_diagonalVandiverPolynomial1381 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381) (i : SourceIndex 1381) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (diagonalVandiverPolynomial1381 i) =
      (diagonalVandiverUnit1381 hzeta i : 𝓞 K) := by
  rw [diagonalVandiverPolynomial1381, Polynomial.eval₂_finsetProd,
    diagonalVandiverUnit1381]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval₂_pow]
  congr 1
  exact eval₂_basicVandiverPolynomial1381 hzeta j

/-! ## Polynomials attached to an arbitrary integer exponent relation -/

/-- The positive polynomial attached to natural exponents `b`.  The outer
factor `1380 = 1381 - 1` is exactly Vandiver's factor in equation (3b). -/
def positiveRelationPolynomial1381
    (b : SourceIndex 1381 → ℕ) : Polynomial ℤ :=
  ∏ i, diagonalVandiverPolynomial1381 i ^ (1380 * b i)

/-- Exponential substitution commutes with the positive relation product. -/
theorem polynomialExp1381_positiveRelationPolynomial1381
    (b : SourceIndex 1381 → ℕ) :
    polynomialExp1381 (positiveRelationPolynomial1381 b) =
      ∏ i,
        Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative.integralDiagonalSeries1381 i ^
          (1380 * b i) := by
  rw [positiveRelationPolynomial1381, polynomialExp1381,
    Polynomial.eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow]
  congr 1
  exact polynomialExp1381_diagonalVandiverPolynomial1381 i

/-- Every diagonal series has nonzero constant coefficient. -/
theorem constantCoeff_integralDiagonalSeries1381_ne_zero
    (i : SourceIndex 1381) :
    PowerSeries.constantCoeff
      (Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative.integralDiagonalSeries1381 i) ≠
        0 := by
  rw [Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative.integralDiagonalSeries1381,
    integralDiagonalExp]
  simp only [map_prod, constantCoeff_integralDiagonalFactor]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact pow_ne_zero _ (by norm_num)

/-- The logarithmic derivative of a positive polynomial product is the
expected natural-exponent sum. -/
theorem logarithmicDerivative_positiveRelationPolynomial1381
    (b : SourceIndex 1381 → ℕ) :
    logarithmicDerivative
        (polynomialExp1381 (positiveRelationPolynomial1381 b)) =
      ∑ i, PowerSeries.C ((1380 * b i : ℕ) : ℚ) *
        logarithmicDerivative
          (Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative.integralDiagonalSeries1381 i) := by
  rw [polynomialExp1381_positiveRelationPolynomial1381 b]
  rw [logarithmicDerivative_prod]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [logarithmicDerivative_pow]
    exact constantCoeff_integralDiagonalSeries1381_ne_zero i
  · intro i hi
    apply constantCoeff_pow_ne_zero
    exact constantCoeff_integralDiagonalSeries1381_ne_zero i

/-- High derivatives of the preceding identity, in the exact normalization
used by `relationDerivative1381`. -/
theorem formalDerivativeAtZero_positiveRelationPolynomial1381
    (b : SourceIndex 1381 → ℕ) (k : SourceIndex 1381) :
    formalDerivativeAtZero
      (Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative.sourceDerivativeOrder1381 k)
      (logarithmicDerivative
        (polynomialExp1381 (positiveRelationPolynomial1381 b))) =
      ∑ i, ((1380 * b i : ℕ) : ℚ) *
        formalDerivativeAtZero
          (Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative.sourceDerivativeOrder1381 k)
          (logarithmicDerivative
            (Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative.integralDiagonalSeries1381 i)) := by
  rw [logarithmicDerivative_positiveRelationPolynomial1381 b,
    formalDerivativeAtZero_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [formalDerivativeAtZero_C_mul]

/-- Clearing negative exponents does not change the source derivative:
the integer relation derivative is the logarithmic derivative of the
positive numerator minus that of the positive denominator. -/
theorem relationDerivative1381_eq_positive_sub_negative
    (a : SourceIndex 1381 → ℤ) (k : SourceIndex 1381) :
    Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative.relationDerivative1381 a k =
      formalDerivativeAtZero
        (Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative.sourceDerivativeOrder1381 k)
        (logarithmicDerivative
          (polynomialExp1381
            (positiveRelationPolynomial1381 (fun i ↦ (a i).toNat)))) -
      formalDerivativeAtZero
        (Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative.sourceDerivativeOrder1381 k)
        (logarithmicDerivative
          (polynomialExp1381
            (positiveRelationPolynomial1381
              (fun i ↦ (-a i).toNat)))) := by
  rw [formalDerivativeAtZero_positiveRelationPolynomial1381,
    formalDerivativeAtZero_positiveRelationPolynomial1381]
  rw [Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative.relationDerivative1381,
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
    (E : SourceIndex 1381 → G) (t : ℕ)
    (a : SourceIndex 1381 → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (∏ i, E i ^ (a i).toNat) =
      u ^ t * ∏ i, E i ^ (-a i).toNat := by
  rw [hrel, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact (zpow_mul_pow_negToNat_eq_pow_toNat (E i) (a i)).symm

/-- The ambient unit represented by the unscaled positive exponent
product.  Its 1380th power is the value of
`positiveRelationPolynomial1381`. -/
def positiveRelationUnit1381 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381)
    (b : SourceIndex 1381 → ℕ) : (𝓞 K)ˣ :=
  ∏ i, diagonalVandiverUnit1381 hzeta i ^ b i

omit [NumberField K] [IsCyclotomicExtension {1381} ℚ K]
    [NumberField.IsCMField K] in
/-- Evaluation of a positive relation polynomial is the 1380th power of
its corresponding unit product. -/
theorem eval₂_positiveRelationPolynomial1381 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381)
    (b : SourceIndex 1381 → ℕ) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial1381 b) =
      (positiveRelationUnit1381 hzeta b ^ 1380 : 𝓞 K) := by
  rw [positiveRelationPolynomial1381, Polynomial.eval₂_finsetProd,
    positiveRelationUnit1381, Units.coe_prod]
  simp_rw [Units.val_pow_eq_pow_val]
  rw [← Finset.prod_pow Finset.univ 1380
    (fun i ↦ (diagonalVandiverUnit1381 hzeta i : 𝓞 K) ^ b i)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow, eval₂_diagonalVandiverPolynomial1381,
    ← pow_mul]
  congr 1
  omega

omit [NumberField K] [IsCyclotomicExtension {1381} ℚ K]
    [NumberField.IsCMField K] in
/-- An actual unit relation gives the exact denominator-cleared evaluation
identity to which the cyclotomic polynomial remainder theorem is applied. -/
theorem eval₂_positive_relation_of_relation {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 1381)
    (u : (𝓞 K)ˣ) (t : ℕ) (a : SourceIndex 1381 → ℤ)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit1381 hzeta i ^ a i) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial1381 (fun i ↦ (a i).toNat)) =
      (u : 𝓞 K) ^ (1380 * t) *
        Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
          (positiveRelationPolynomial1381 (fun i ↦ (-a i).toNat)) := by
  rw [eval₂_positiveRelationPolynomial1381,
    eval₂_positiveRelationPolynomial1381]
  have hpos := positive_relation_of_zpow_relation
    (E := diagonalVandiverUnit1381 hzeta) t a hrel
  have hpow := congrArg (fun x : (𝓞 K)ˣ ↦ x ^ 1380) hpos
  have hval := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hpow
  simpa only [positiveRelationUnit1381, Units.val_pow_eq_pow_val,
    Units.val_mul, mul_pow, ← pow_mul, Nat.mul_comm] using hval

end

end Fermat.OneThousandThreeHundredEightyOne.VandiverPolynomialUnits
