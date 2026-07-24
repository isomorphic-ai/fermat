import Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative691
import Fermat.SixHundredNinetyOne.VandiverDiagonalUnits691

/-!
# Vandiver's integral unit polynomials at exponent 691

This file identifies the two incarnations of the diagonal units used in
Vandiver's Lemma II.

For a positive integer `s`, put

`epsilon_s(W) = W^(287*s) * (1 + W^s + ... + W^(4954*s))`.

At `W = zeta`, these are the literal normalized circular units used in
`VandiverDiagonalUnits691`.  After the formal substitution `W = exp V`,
they are the normalized geometric exponential series used in
`VandiverDiagonalDerivative691`.
-/

open scoped BigOperators NumberField

namespace Fermat.SixHundredNinetyOne.VandiverPolynomialUnits

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.SixHundredNinetyOne.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

set_option maxRecDepth 100000

/-- Formal substitution of `exp V` into an integer polynomial. -/
def polynomialExp691 (P : Polynomial ℤ) : PowerSeries ℚ :=
  Polynomial.eval₂ (algebraMap ℤ (PowerSeries ℚ))
    (PowerSeries.exp ℚ) P

/-- Vandiver's basic integral polynomial
`W^(287*s) * (1 + W^s + ... + W^(4954*s))`. -/
def basicVandiverPolynomial691 (s : ℕ) : Polynomial ℤ :=
  Polynomial.X ^ (287 * s) *
    ∑ j ∈ Finset.range 4955, Polynomial.X ^ (s * j)

/-- Substitution `W = exp V` turns the basic integral polynomial into
the normalized geometric exponential used in the derivative calculation. -/
theorem polynomialExp691_basicVandiverPolynomial691 (s : ℕ) :
    polynomialExp691 (basicVandiverPolynomial691 s) =
      normalizedGeomExp 4955 287 s := by
  rw [polynomialExp691, basicVandiverPolynomial691, Polynomial.eval₂_mul,
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
theorem eval₂_basicVandiverPolynomial691 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691)
    (j : VandiverFactorIndex691) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (basicVandiverPolynomial691 (conjugateExponent691 j)) =
      (basicVandiverUnit691 hzeta j : 𝓞 K) := by
  rw [basicVandiverUnit691,
    Fermat.Irregular.CircularUnitFamily.normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [basicVandiverPolynomial691, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_finsetSum]
  congr 1 <;> simp only [← pow_mul] <;> ring_nf

/-- Vandiver's positive integral polynomial representing the `i`th
diagonal unit. -/
def diagonalVandiverPolynomial691
    (i : SourceIndex 691) : Polynomial ℤ :=
  ∏ j : VandiverFactorIndex691,
    basicVandiverPolynomial691 (conjugateExponent691 j) ^
      diagonalWeight691 i j

/-- The exponential substitution of the actual diagonal polynomial is
the formal diagonal series used in the derivative theorem. -/
theorem polynomialExp691_diagonalVandiverPolynomial691
    (i : SourceIndex 691) :
    polynomialExp691 (diagonalVandiverPolynomial691 i) =
      Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative.integralDiagonalSeries691 i := by
  rw [diagonalVandiverPolynomial691, polynomialExp691,
    Polynomial.eval₂_finsetProd]
  simp_rw [Polynomial.eval₂_pow]
  rw [Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative.integralDiagonalSeries691,
    integralDiagonalExp]
  norm_num
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [dif_pos hj]
  simp only [integralDiagonalFactor, diagonalWeight691,
    conjugateExponent691, sourceNumber]
  change
    (polynomialExp691 (basicVandiverPolynomial691 (4955 ^ j))) ^
          integralDiagonalWeight 691 4955 (i.val + 1) j =
      normalizedGeomExp 4955 287 (4955 ^ j) ^
          integralDiagonalWeight 691 4955 (i.val + 1) j
  rw [polynomialExp691_basicVandiverPolynomial691]

variable [NumberField K] [IsCyclotomicExtension {691} ℚ K]
  [NumberField.IsCMField K]

/-- Evaluation at the chosen primitive root gives the literal ambient
diagonal unit constructed in `VandiverDiagonalUnits691`. -/
theorem eval₂_diagonalVandiverPolynomial691 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691) (i : SourceIndex 691) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (diagonalVandiverPolynomial691 i) =
      (diagonalVandiverUnit691 hzeta i : 𝓞 K) := by
  rw [diagonalVandiverPolynomial691, Polynomial.eval₂_finsetProd,
    diagonalVandiverUnit691]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval₂_pow]
  congr 1
  exact eval₂_basicVandiverPolynomial691 hzeta j

/-! ## Polynomials attached to an arbitrary integer exponent relation -/

/-- The positive polynomial attached to natural exponents `b`.  The outer
factor `690 = 691 - 1` is exactly Vandiver's factor in equation (3b). -/
def positiveRelationPolynomial691
    (b : SourceIndex 691 → ℕ) : Polynomial ℤ :=
  ∏ i, diagonalVandiverPolynomial691 i ^ (690 * b i)

/-- Exponential substitution commutes with the positive relation product. -/
theorem polynomialExp691_positiveRelationPolynomial691
    (b : SourceIndex 691 → ℕ) :
    polynomialExp691 (positiveRelationPolynomial691 b) =
      ∏ i,
        Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative.integralDiagonalSeries691 i ^
          (690 * b i) := by
  rw [positiveRelationPolynomial691, polynomialExp691,
    Polynomial.eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow]
  congr 1
  exact polynomialExp691_diagonalVandiverPolynomial691 i

/-- Every diagonal series has nonzero constant coefficient. -/
theorem constantCoeff_integralDiagonalSeries691_ne_zero
    (i : SourceIndex 691) :
    PowerSeries.constantCoeff
      (Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative.integralDiagonalSeries691 i) ≠
        0 := by
  rw [Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative.integralDiagonalSeries691,
    integralDiagonalExp]
  simp only [map_prod, constantCoeff_integralDiagonalFactor]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact pow_ne_zero _ (by norm_num)

/-- The logarithmic derivative of a positive polynomial product is the
expected natural-exponent sum. -/
theorem logarithmicDerivative_positiveRelationPolynomial691
    (b : SourceIndex 691 → ℕ) :
    logarithmicDerivative
        (polynomialExp691 (positiveRelationPolynomial691 b)) =
      ∑ i, PowerSeries.C ((690 * b i : ℕ) : ℚ) *
        logarithmicDerivative
          (Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative.integralDiagonalSeries691 i) := by
  rw [polynomialExp691_positiveRelationPolynomial691 b]
  rw [logarithmicDerivative_prod]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [logarithmicDerivative_pow]
    exact constantCoeff_integralDiagonalSeries691_ne_zero i
  · intro i hi
    apply constantCoeff_pow_ne_zero
    exact constantCoeff_integralDiagonalSeries691_ne_zero i

/-- High derivatives of the preceding identity, in the exact normalization
used by `relationDerivative691`. -/
theorem formalDerivativeAtZero_positiveRelationPolynomial691
    (b : SourceIndex 691 → ℕ) (k : SourceIndex 691) :
    formalDerivativeAtZero
      (Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative.sourceDerivativeOrder691 k)
      (logarithmicDerivative
        (polynomialExp691 (positiveRelationPolynomial691 b))) =
      ∑ i, ((690 * b i : ℕ) : ℚ) *
        formalDerivativeAtZero
          (Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative.sourceDerivativeOrder691 k)
          (logarithmicDerivative
            (Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative.integralDiagonalSeries691 i)) := by
  rw [logarithmicDerivative_positiveRelationPolynomial691 b,
    formalDerivativeAtZero_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [formalDerivativeAtZero_C_mul]

/-- Clearing negative exponents does not change the source derivative:
the integer relation derivative is the logarithmic derivative of the
positive numerator minus that of the positive denominator. -/
theorem relationDerivative691_eq_positive_sub_negative
    (a : SourceIndex 691 → ℤ) (k : SourceIndex 691) :
    Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative.relationDerivative691 a k =
      formalDerivativeAtZero
        (Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative.sourceDerivativeOrder691 k)
        (logarithmicDerivative
          (polynomialExp691
            (positiveRelationPolynomial691 (fun i ↦ (a i).toNat)))) -
      formalDerivativeAtZero
        (Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative.sourceDerivativeOrder691 k)
        (logarithmicDerivative
          (polynomialExp691
            (positiveRelationPolynomial691
              (fun i ↦ (-a i).toNat)))) := by
  rw [formalDerivativeAtZero_positiveRelationPolynomial691,
    formalDerivativeAtZero_positiveRelationPolynomial691]
  rw [Fermat.SixHundredNinetyOne.VandiverDiagonalDerivative.relationDerivative691,
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
    (E : SourceIndex 691 → G) (t : ℕ)
    (a : SourceIndex 691 → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (∏ i, E i ^ (a i).toNat) =
      u ^ t * ∏ i, E i ^ (-a i).toNat := by
  rw [hrel, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact (zpow_mul_pow_negToNat_eq_pow_toNat (E i) (a i)).symm

/-- The ambient unit represented by the unscaled positive exponent
product.  Its 690th power is the value of
`positiveRelationPolynomial691`. -/
def positiveRelationUnit691 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691)
    (b : SourceIndex 691 → ℕ) : (𝓞 K)ˣ :=
  ∏ i, diagonalVandiverUnit691 hzeta i ^ b i

/-- Evaluation of a positive relation polynomial is the 690th power of
its corresponding unit product. -/
theorem eval₂_positiveRelationPolynomial691 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691)
    (b : SourceIndex 691 → ℕ) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial691 b) =
      (positiveRelationUnit691 hzeta b ^ 690 : 𝓞 K) := by
  rw [positiveRelationPolynomial691, Polynomial.eval₂_finsetProd,
    positiveRelationUnit691, Units.coe_prod]
  simp_rw [Units.val_pow_eq_pow_val]
  rw [← Finset.prod_pow Finset.univ 690
    (fun i ↦ (diagonalVandiverUnit691 hzeta i : 𝓞 K) ^ b i)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow, eval₂_diagonalVandiverPolynomial691,
    ← pow_mul]
  congr 1
  omega

/-- An actual unit relation gives the exact denominator-cleared evaluation
identity to which the cyclotomic polynomial remainder theorem is applied. -/
theorem eval₂_positive_relation_of_relation {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 691)
    (u : (𝓞 K)ˣ) (t : ℕ) (a : SourceIndex 691 → ℤ)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit691 hzeta i ^ a i) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial691 (fun i ↦ (a i).toNat)) =
      (u : 𝓞 K) ^ (690 * t) *
        Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
          (positiveRelationPolynomial691 (fun i ↦ (-a i).toNat)) := by
  rw [eval₂_positiveRelationPolynomial691,
    eval₂_positiveRelationPolynomial691]
  have hpos := positive_relation_of_zpow_relation
    (E := diagonalVandiverUnit691 hzeta) t a hrel
  have hpow := congrArg (fun x : (𝓞 K)ˣ ↦ x ^ 690) hpos
  have hval := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hpow
  simpa only [positiveRelationUnit691, Units.val_pow_eq_pow_val,
    Units.val_mul, mul_pow, ← pow_mul, Nat.mul_comm] using hval

end

end Fermat.SixHundredNinetyOne.VandiverPolynomialUnits
