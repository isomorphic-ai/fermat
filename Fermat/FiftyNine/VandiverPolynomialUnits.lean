import Fermat.FiftyNine.VandiverDiagonalDerivative
import Fermat.FiftyNine.VandiverDiagonalUnits

/-!
# Vandiver's integral unit polynomials at exponent 59

This file identifies the two incarnations of the diagonal units used in
Vandiver's Lemma II.

For a positive integer `s`, put

`epsilon_s(W) = W^(29*s) * (1 + W^s + ... + W^(945*s))`.

At `W = zeta`, these are the literal normalized circular units used in
`VandiverDiagonalUnits`.  After the formal substitution `W = exp V`, they
are the normalized geometric exponential series used in
`VandiverDiagonalDerivative`.  Thus the integral diagonal polynomial below
is simultaneously

* Vandiver's actual algebraic unit when evaluated at `zeta`; and
* the already diagonalized formal power series when evaluated at `exp V`.

This is the algebraic/formal bridge needed for the polynomial-remainder
calculation on pp. 617--621 of Vandiver's 1929 paper.
-/

open scoped BigOperators NumberField

namespace Fermat.FiftyNine.VandiverPolynomialUnits

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.FiftyNine.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

set_option maxRecDepth 100000

/-- Formal substitution of `exp V` into an integer polynomial. -/
def polynomialExp59 (P : Polynomial ℤ) : PowerSeries ℚ :=
  Polynomial.eval₂ (algebraMap ℤ (PowerSeries ℚ))
    (PowerSeries.exp ℚ) P

/-- Vandiver's basic integral polynomial
`W^(29*s) * (1 + W^s + ... + W^(945*s))`. -/
def basicVandiverPolynomial59 (s : ℕ) : Polynomial ℤ :=
  Polynomial.X ^ (29 * s) *
    ∑ j ∈ Finset.range 946, Polynomial.X ^ (s * j)

/-- Substitution `W = exp V` turns the basic integral polynomial into
the normalized geometric exponential used in the derivative calculation. -/
theorem polynomialExp59_basicVandiverPolynomial59 (s : ℕ) :
    polynomialExp59 (basicVandiverPolynomial59 s) =
      normalizedGeomExp 946 29 s := by
  rw [polynomialExp59, basicVandiverPolynomial59, Polynomial.eval₂_mul,
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
theorem eval₂_basicVandiverPolynomial59 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59)
    (j : VandiverFactorIndex59) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (basicVandiverPolynomial59 (conjugateExponent59 j)) =
      (basicVandiverUnit59 hzeta j : 𝓞 K) := by
  rw [basicVandiverUnit59,
    Fermat.Irregular.CircularUnitFamily.normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [basicVandiverPolynomial59, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_finsetSum]
  congr 1 <;> simp only [← pow_mul] <;> ring_nf

/-- Vandiver's positive integral polynomial representing the `i`th
diagonal unit. -/
def diagonalVandiverPolynomial59
    (i : SourceIndex 59) : Polynomial ℤ :=
  ∏ j : VandiverFactorIndex59,
    basicVandiverPolynomial59 (conjugateExponent59 j) ^
      diagonalWeight59 i j

/-- The exponential substitution of the actual diagonal polynomial is
definitionally the formal diagonal series used in the derivative theorem. -/
theorem polynomialExp59_diagonalVandiverPolynomial59
    (i : SourceIndex 59) :
    polynomialExp59 (diagonalVandiverPolynomial59 i) =
      Fermat.FiftyNine.VandiverDiagonalDerivative.integralDiagonalSeries59 i := by
  rw [diagonalVandiverPolynomial59, polynomialExp59,
    Polynomial.eval₂_finsetProd]
  simp_rw [Polynomial.eval₂_pow]
  rw [Fermat.FiftyNine.VandiverDiagonalDerivative.integralDiagonalSeries59,
    integralDiagonalExp]
  norm_num
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [dif_pos hj]
  simp only [integralDiagonalFactor, diagonalWeight59,
    conjugateExponent59, sourceNumber]
  change
    (polynomialExp59 (basicVandiverPolynomial59 (946 ^ j))) ^
          integralDiagonalWeight 59 946 (i.val + 1) j =
      normalizedGeomExp 946 29 (946 ^ j) ^
          integralDiagonalWeight 59 946 (i.val + 1) j
  rw [polynomialExp59_basicVandiverPolynomial59]

variable [NumberField K] [IsCyclotomicExtension {59} ℚ K]
  [NumberField.IsCMField K]

/-- Evaluation at the chosen primitive root gives the literal ambient
diagonal unit constructed in `VandiverDiagonalUnits`. -/
theorem eval₂_diagonalVandiverPolynomial59 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59) (i : SourceIndex 59) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (diagonalVandiverPolynomial59 i) =
      (diagonalVandiverUnit59 hzeta i : 𝓞 K) := by
  rw [diagonalVandiverPolynomial59, Polynomial.eval₂_finsetProd,
    diagonalVandiverUnit59]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval₂_pow]
  congr 1
  exact eval₂_basicVandiverPolynomial59 hzeta j

/-! ## Polynomials attached to an arbitrary integer exponent relation -/

/-- The positive polynomial attached to natural exponents `b`.  The outer
factor `58 = 59 - 1` is exactly Vandiver's factor in equation (3b). -/
def positiveRelationPolynomial59
    (b : SourceIndex 59 → ℕ) : Polynomial ℤ :=
  ∏ i, diagonalVandiverPolynomial59 i ^ (58 * b i)

/-- Exponential substitution commutes with the positive relation product. -/
theorem polynomialExp59_positiveRelationPolynomial59
    (b : SourceIndex 59 → ℕ) :
    polynomialExp59 (positiveRelationPolynomial59 b) =
      ∏ i,
        Fermat.FiftyNine.VandiverDiagonalDerivative.integralDiagonalSeries59 i ^
          (58 * b i) := by
  rw [positiveRelationPolynomial59, polynomialExp59,
    Polynomial.eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow]
  congr 1
  exact polynomialExp59_diagonalVandiverPolynomial59 i

/-- Every diagonal series has nonzero constant coefficient. -/
theorem constantCoeff_integralDiagonalSeries59_ne_zero
    (i : SourceIndex 59) :
    PowerSeries.constantCoeff
      (Fermat.FiftyNine.VandiverDiagonalDerivative.integralDiagonalSeries59 i) ≠
        0 := by
  rw [Fermat.FiftyNine.VandiverDiagonalDerivative.integralDiagonalSeries59,
    integralDiagonalExp]
  simp only [map_prod, constantCoeff_integralDiagonalFactor]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact pow_ne_zero _ (by norm_num)

/-- The logarithmic derivative of a positive polynomial product is the
expected natural-exponent sum. -/
theorem logarithmicDerivative_positiveRelationPolynomial59
    (b : SourceIndex 59 → ℕ) :
    logarithmicDerivative
        (polynomialExp59 (positiveRelationPolynomial59 b)) =
      ∑ i, PowerSeries.C ((58 * b i : ℕ) : ℚ) *
        logarithmicDerivative
          (Fermat.FiftyNine.VandiverDiagonalDerivative.integralDiagonalSeries59 i) := by
  rw [polynomialExp59_positiveRelationPolynomial59 b]
  rw [logarithmicDerivative_prod]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [logarithmicDerivative_pow]
    exact constantCoeff_integralDiagonalSeries59_ne_zero i
  · intro i hi
    apply constantCoeff_pow_ne_zero
    exact constantCoeff_integralDiagonalSeries59_ne_zero i

/-- High derivatives of the preceding identity, in the exact normalization
used by `relationDerivative59`. -/
theorem formalDerivativeAtZero_positiveRelationPolynomial59
    (b : SourceIndex 59 → ℕ) (k : SourceIndex 59) :
    formalDerivativeAtZero
      (Fermat.FiftyNine.VandiverDiagonalDerivative.sourceDerivativeOrder59 k)
      (logarithmicDerivative
        (polynomialExp59 (positiveRelationPolynomial59 b))) =
      ∑ i, ((58 * b i : ℕ) : ℚ) *
        formalDerivativeAtZero
          (Fermat.FiftyNine.VandiverDiagonalDerivative.sourceDerivativeOrder59 k)
          (logarithmicDerivative
            (Fermat.FiftyNine.VandiverDiagonalDerivative.integralDiagonalSeries59 i)) := by
  rw [logarithmicDerivative_positiveRelationPolynomial59 b,
    formalDerivativeAtZero_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [formalDerivativeAtZero_C_mul]

/-- Clearing negative exponents does not change the source derivative:
the integer relation derivative is the logarithmic derivative of the
positive numerator minus that of the positive denominator. -/
theorem relationDerivative59_eq_positive_sub_negative
    (a : SourceIndex 59 → ℤ) (k : SourceIndex 59) :
    Fermat.FiftyNine.VandiverDiagonalDerivative.relationDerivative59 a k =
      formalDerivativeAtZero
        (Fermat.FiftyNine.VandiverDiagonalDerivative.sourceDerivativeOrder59 k)
        (logarithmicDerivative
          (polynomialExp59
            (positiveRelationPolynomial59 (fun i ↦ (a i).toNat)))) -
      formalDerivativeAtZero
        (Fermat.FiftyNine.VandiverDiagonalDerivative.sourceDerivativeOrder59 k)
        (logarithmicDerivative
          (polynomialExp59
            (positiveRelationPolynomial59
              (fun i ↦ (-a i).toNat)))) := by
  rw [formalDerivativeAtZero_positiveRelationPolynomial59,
    formalDerivativeAtZero_positiveRelationPolynomial59]
  rw [Fermat.FiftyNine.VandiverDiagonalDerivative.relationDerivative59,
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
    (E : SourceIndex 59 → G) (t : ℕ)
    (a : SourceIndex 59 → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (∏ i, E i ^ (a i).toNat) =
      u ^ t * ∏ i, E i ^ (-a i).toNat := by
  rw [hrel, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact (zpow_mul_pow_negToNat_eq_pow_toNat (E i) (a i)).symm

/-- The ambient unit represented by the unscaled positive exponent
product.  Its 58th power is the value of
`positiveRelationPolynomial59`. -/
def positiveRelationUnit59 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59)
    (b : SourceIndex 59 → ℕ) : (𝓞 K)ˣ :=
  ∏ i, diagonalVandiverUnit59 hzeta i ^ b i

/-- Evaluation of a positive relation polynomial is the 58th power of
its corresponding unit product. -/
theorem eval₂_positiveRelationPolynomial59 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59)
    (b : SourceIndex 59 → ℕ) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial59 b) =
      (positiveRelationUnit59 hzeta b ^ 58 : 𝓞 K) := by
  rw [positiveRelationPolynomial59, Polynomial.eval₂_finsetProd,
    positiveRelationUnit59, Units.coe_prod]
  simp_rw [Units.val_pow_eq_pow_val]
  rw [← Finset.prod_pow Finset.univ 58
    (fun i ↦ (diagonalVandiverUnit59 hzeta i : 𝓞 K) ^ b i)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow, eval₂_diagonalVandiverPolynomial59,
    ← pow_mul]
  congr 1
  omega

/-- An actual unit relation gives the exact denominator-cleared evaluation
identity to which the cyclotomic polynomial remainder theorem is applied. -/
theorem eval₂_positive_relation_of_relation {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 59)
    (u : (𝓞 K)ˣ) (t : ℕ) (a : SourceIndex 59 → ℤ)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit59 hzeta i ^ a i) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial59 (fun i ↦ (a i).toNat)) =
      (u : 𝓞 K) ^ (58 * t) *
        Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
          (positiveRelationPolynomial59 (fun i ↦ (-a i).toNat)) := by
  rw [eval₂_positiveRelationPolynomial59,
    eval₂_positiveRelationPolynomial59]
  have hpos := positive_relation_of_zpow_relation
    (E := diagonalVandiverUnit59 hzeta) t a hrel
  have hpow := congrArg (fun x : (𝓞 K)ˣ ↦ x ^ 58) hpos
  have hval := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hpow
  simpa only [positiveRelationUnit59, Units.val_pow_eq_pow_val,
    Units.val_mul, mul_pow, ← pow_mul, Nat.mul_comm] using hval

end

end Fermat.FiftyNine.VandiverPolynomialUnits
