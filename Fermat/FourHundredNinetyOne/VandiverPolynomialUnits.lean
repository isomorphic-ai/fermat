import Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative491
import Fermat.FourHundredNinetyOne.VandiverDiagonalUnits491

/-!
# Vandiver's integral unit polynomials at exponent 491

This file identifies the two incarnations of the diagonal units used in
Vandiver's Lemma II.

For a positive integer `s`, put

`epsilon_s(W) = W^(463*s) * (1 + W^s + ... + W^(2511*s))`.

At `W = zeta`, these are the literal normalized circular units used in
`VandiverDiagonalUnits491`.  After the formal substitution `W = exp V`,
they are the normalized geometric exponential series used in
`VandiverDiagonalDerivative491`.
-/

open scoped BigOperators NumberField

namespace Fermat.FourHundredNinetyOne.VandiverPolynomialUnits

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.FourHundredNinetyOne.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

set_option maxRecDepth 100000

/-- Formal substitution of `exp V` into an integer polynomial. -/
def polynomialExp491 (P : Polynomial ℤ) : PowerSeries ℚ :=
  Polynomial.eval₂ (algebraMap ℤ (PowerSeries ℚ))
    (PowerSeries.exp ℚ) P

/-- Vandiver's basic integral polynomial
`W^(463*s) * (1 + W^s + ... + W^(2511*s))`. -/
def basicVandiverPolynomial491 (s : ℕ) : Polynomial ℤ :=
  Polynomial.X ^ (463 * s) *
    ∑ j ∈ Finset.range 2512, Polynomial.X ^ (s * j)

/-- Substitution `W = exp V` turns the basic integral polynomial into
the normalized geometric exponential used in the derivative calculation. -/
theorem polynomialExp491_basicVandiverPolynomial491 (s : ℕ) :
    polynomialExp491 (basicVandiverPolynomial491 s) =
      normalizedGeomExp 2512 463 s := by
  rw [polynomialExp491, basicVandiverPolynomial491, Polynomial.eval₂_mul,
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
theorem eval₂_basicVandiverPolynomial491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491)
    (j : VandiverFactorIndex491) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (basicVandiverPolynomial491 (conjugateExponent491 j)) =
      (basicVandiverUnit491 hzeta j : 𝓞 K) := by
  rw [basicVandiverUnit491,
    Fermat.Irregular.CircularUnitFamily.normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [basicVandiverPolynomial491, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_finsetSum]
  congr 1 <;> simp only [← pow_mul] <;> ring_nf

/-- Vandiver's positive integral polynomial representing the `i`th
diagonal unit. -/
def diagonalVandiverPolynomial491
    (i : SourceIndex 491) : Polynomial ℤ :=
  ∏ j : VandiverFactorIndex491,
    basicVandiverPolynomial491 (conjugateExponent491 j) ^
      diagonalWeight491 i j

/-- The exponential substitution of the actual diagonal polynomial is
the formal diagonal series used in the derivative theorem. -/
theorem polynomialExp491_diagonalVandiverPolynomial491
    (i : SourceIndex 491) :
    polynomialExp491 (diagonalVandiverPolynomial491 i) =
      Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative.integralDiagonalSeries491 i := by
  rw [diagonalVandiverPolynomial491, polynomialExp491,
    Polynomial.eval₂_finsetProd]
  simp_rw [Polynomial.eval₂_pow]
  rw [Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative.integralDiagonalSeries491,
    integralDiagonalExp]
  norm_num
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [dif_pos hj]
  simp only [integralDiagonalFactor, diagonalWeight491,
    conjugateExponent491, sourceNumber]
  change
    (polynomialExp491 (basicVandiverPolynomial491 (2512 ^ j))) ^
          integralDiagonalWeight 491 2512 (i.val + 1) j =
      normalizedGeomExp 2512 463 (2512 ^ j) ^
          integralDiagonalWeight 491 2512 (i.val + 1) j
  rw [polynomialExp491_basicVandiverPolynomial491]

variable [NumberField K] [IsCyclotomicExtension {491} ℚ K]
  [NumberField.IsCMField K]

/-- Evaluation at the chosen primitive root gives the literal ambient
diagonal unit constructed in `VandiverDiagonalUnits491`. -/
theorem eval₂_diagonalVandiverPolynomial491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) (i : SourceIndex 491) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (diagonalVandiverPolynomial491 i) =
      (diagonalVandiverUnit491 hzeta i : 𝓞 K) := by
  rw [diagonalVandiverPolynomial491, Polynomial.eval₂_finsetProd,
    diagonalVandiverUnit491]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval₂_pow]
  congr 1
  exact eval₂_basicVandiverPolynomial491 hzeta j

/-! ## Polynomials attached to an arbitrary integer exponent relation -/

/-- The positive polynomial attached to natural exponents `b`.  The outer
factor `490 = 491 - 1` is exactly Vandiver's factor in equation (3b). -/
def positiveRelationPolynomial491
    (b : SourceIndex 491 → ℕ) : Polynomial ℤ :=
  ∏ i, diagonalVandiverPolynomial491 i ^ (490 * b i)

/-- Exponential substitution commutes with the positive relation product. -/
theorem polynomialExp491_positiveRelationPolynomial491
    (b : SourceIndex 491 → ℕ) :
    polynomialExp491 (positiveRelationPolynomial491 b) =
      ∏ i,
        Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative.integralDiagonalSeries491 i ^
          (490 * b i) := by
  rw [positiveRelationPolynomial491, polynomialExp491,
    Polynomial.eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow]
  congr 1
  exact polynomialExp491_diagonalVandiverPolynomial491 i

/-- Every diagonal series has nonzero constant coefficient. -/
theorem constantCoeff_integralDiagonalSeries491_ne_zero
    (i : SourceIndex 491) :
    PowerSeries.constantCoeff
      (Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative.integralDiagonalSeries491 i) ≠
        0 := by
  rw [Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative.integralDiagonalSeries491,
    integralDiagonalExp]
  simp only [map_prod, constantCoeff_integralDiagonalFactor]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact pow_ne_zero _ (by norm_num)

/-- The logarithmic derivative of a positive polynomial product is the
expected natural-exponent sum. -/
theorem logarithmicDerivative_positiveRelationPolynomial491
    (b : SourceIndex 491 → ℕ) :
    logarithmicDerivative
        (polynomialExp491 (positiveRelationPolynomial491 b)) =
      ∑ i, PowerSeries.C ((490 * b i : ℕ) : ℚ) *
        logarithmicDerivative
          (Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative.integralDiagonalSeries491 i) := by
  rw [polynomialExp491_positiveRelationPolynomial491 b]
  rw [logarithmicDerivative_prod]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [logarithmicDerivative_pow]
    exact constantCoeff_integralDiagonalSeries491_ne_zero i
  · intro i hi
    apply constantCoeff_pow_ne_zero
    exact constantCoeff_integralDiagonalSeries491_ne_zero i

/-- High derivatives of the preceding identity, in the exact normalization
used by `relationDerivative491`. -/
theorem formalDerivativeAtZero_positiveRelationPolynomial491
    (b : SourceIndex 491 → ℕ) (k : SourceIndex 491) :
    formalDerivativeAtZero
      (Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative.sourceDerivativeOrder491 k)
      (logarithmicDerivative
        (polynomialExp491 (positiveRelationPolynomial491 b))) =
      ∑ i, ((490 * b i : ℕ) : ℚ) *
        formalDerivativeAtZero
          (Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative.sourceDerivativeOrder491 k)
          (logarithmicDerivative
            (Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative.integralDiagonalSeries491 i)) := by
  rw [logarithmicDerivative_positiveRelationPolynomial491 b,
    formalDerivativeAtZero_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [formalDerivativeAtZero_C_mul]

/-- Clearing negative exponents does not change the source derivative:
the integer relation derivative is the logarithmic derivative of the
positive numerator minus that of the positive denominator. -/
theorem relationDerivative491_eq_positive_sub_negative
    (a : SourceIndex 491 → ℤ) (k : SourceIndex 491) :
    Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative.relationDerivative491 a k =
      formalDerivativeAtZero
        (Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative.sourceDerivativeOrder491 k)
        (logarithmicDerivative
          (polynomialExp491
            (positiveRelationPolynomial491 (fun i ↦ (a i).toNat)))) -
      formalDerivativeAtZero
        (Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative.sourceDerivativeOrder491 k)
        (logarithmicDerivative
          (polynomialExp491
            (positiveRelationPolynomial491
              (fun i ↦ (-a i).toNat)))) := by
  rw [formalDerivativeAtZero_positiveRelationPolynomial491,
    formalDerivativeAtZero_positiveRelationPolynomial491]
  rw [Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative.relationDerivative491,
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
    (E : SourceIndex 491 → G) (t : ℕ)
    (a : SourceIndex 491 → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (∏ i, E i ^ (a i).toNat) =
      u ^ t * ∏ i, E i ^ (-a i).toNat := by
  rw [hrel, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact (zpow_mul_pow_negToNat_eq_pow_toNat (E i) (a i)).symm

/-- The ambient unit represented by the unscaled positive exponent
product.  Its 490th power is the value of
`positiveRelationPolynomial491`. -/
def positiveRelationUnit491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491)
    (b : SourceIndex 491 → ℕ) : (𝓞 K)ˣ :=
  ∏ i, diagonalVandiverUnit491 hzeta i ^ b i

/-- Evaluation of a positive relation polynomial is the 490th power of
its corresponding unit product. -/
theorem eval₂_positiveRelationPolynomial491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491)
    (b : SourceIndex 491 → ℕ) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial491 b) =
      (positiveRelationUnit491 hzeta b ^ 490 : 𝓞 K) := by
  rw [positiveRelationPolynomial491, Polynomial.eval₂_finsetProd,
    positiveRelationUnit491, Units.coe_prod]
  simp_rw [Units.val_pow_eq_pow_val]
  rw [← Finset.prod_pow Finset.univ 490
    (fun i ↦ (diagonalVandiverUnit491 hzeta i : 𝓞 K) ^ b i)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow, eval₂_diagonalVandiverPolynomial491,
    ← pow_mul]
  congr 1
  omega

/-- An actual unit relation gives the exact denominator-cleared evaluation
identity to which the cyclotomic polynomial remainder theorem is applied. -/
theorem eval₂_positive_relation_of_relation {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491)
    (u : (𝓞 K)ˣ) (t : ℕ) (a : SourceIndex 491 → ℤ)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit491 hzeta i ^ a i) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial491 (fun i ↦ (a i).toNat)) =
      (u : 𝓞 K) ^ (490 * t) *
        Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
          (positiveRelationPolynomial491 (fun i ↦ (-a i).toNat)) := by
  rw [eval₂_positiveRelationPolynomial491,
    eval₂_positiveRelationPolynomial491]
  have hpos := positive_relation_of_zpow_relation
    (E := diagonalVandiverUnit491 hzeta) t a hrel
  have hpow := congrArg (fun x : (𝓞 K)ˣ ↦ x ^ 490) hpos
  have hval := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hpow
  simpa only [positiveRelationUnit491, Units.val_pow_eq_pow_val,
    Units.val_mul, mul_pow, ← pow_mul, Nat.mul_comm] using hval

end

end Fermat.FourHundredNinetyOne.VandiverPolynomialUnits
