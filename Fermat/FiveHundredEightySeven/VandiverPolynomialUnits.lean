import Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative587
import Fermat.FiveHundredEightySeven.VandiverDiagonalUnits587

/-!
# Vandiver's integral unit polynomials at exponent 587

This file identifies the two incarnations of the diagonal units used in
Vandiver's Lemma II.

For a positive integer `s`, put

`epsilon_s(W) = W^(258*s) * (1 + W^s + ... + W^(6528*s))`.

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

namespace Fermat.FiveHundredEightySeven.VandiverPolynomialUnits

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.FiveHundredEightySeven.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩

set_option maxRecDepth 100000

/-- Formal substitution of `exp V` into an integer polynomial. -/
def polynomialExp587 (P : Polynomial ℤ) : PowerSeries ℚ :=
  Polynomial.eval₂ (algebraMap ℤ (PowerSeries ℚ))
    (PowerSeries.exp ℚ) P

/-- Vandiver's basic integral polynomial
`W^(258*s) * (1 + W^s + ... + W^(6528*s))`. -/
def basicVandiverPolynomial587 (s : ℕ) : Polynomial ℤ :=
  Polynomial.X ^ (258 * s) *
    ∑ j ∈ Finset.range 6529, Polynomial.X ^ (s * j)

/-- Substitution `W = exp V` turns the basic integral polynomial into
the normalized geometric exponential used in the derivative calculation. -/
theorem polynomialExp587_basicVandiverPolynomial587 (s : ℕ) :
    polynomialExp587 (basicVandiverPolynomial587 s) =
      normalizedGeomExp 6529 258 s := by
  rw [polynomialExp587, basicVandiverPolynomial587, Polynomial.eval₂_mul,
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
theorem eval₂_basicVandiverPolynomial587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587)
    (j : VandiverFactorIndex587) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (basicVandiverPolynomial587 (conjugateExponent587 j)) =
      (basicVandiverUnit587 hzeta j : 𝓞 K) := by
  rw [basicVandiverUnit587,
    Fermat.Irregular.CircularUnitFamily.normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [basicVandiverPolynomial587, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_finsetSum]
  congr 1 <;> simp only [← pow_mul] <;> ring_nf

/-- Vandiver's positive integral polynomial representing the `i`th
diagonal unit. -/
def diagonalVandiverPolynomial587
    (i : SourceIndex 587) : Polynomial ℤ :=
  ∏ j : VandiverFactorIndex587,
    basicVandiverPolynomial587 (conjugateExponent587 j) ^
      diagonalWeight587 i j

/-- The exponential substitution of the actual diagonal polynomial is
definitionally the formal diagonal series used in the derivative theorem. -/
theorem polynomialExp587_diagonalVandiverPolynomial587
    (i : SourceIndex 587) :
    polynomialExp587 (diagonalVandiverPolynomial587 i) =
      Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative.integralDiagonalSeries587 i := by
  rw [diagonalVandiverPolynomial587, polynomialExp587,
    Polynomial.eval₂_finsetProd]
  simp_rw [Polynomial.eval₂_pow]
  rw [Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative.integralDiagonalSeries587,
    integralDiagonalExp]
  norm_num
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [dif_pos hj]
  simp only [integralDiagonalFactor, diagonalWeight587,
    conjugateExponent587, sourceNumber]
  change
    (polynomialExp587 (basicVandiverPolynomial587 (6529 ^ j))) ^
          integralDiagonalWeight 587 6529 (i.val + 1) j =
      normalizedGeomExp 6529 258 (6529 ^ j) ^
          integralDiagonalWeight 587 6529 (i.val + 1) j
  rw [polynomialExp587_basicVandiverPolynomial587]

variable [NumberField K] [IsCyclotomicExtension {587} ℚ K]
  [NumberField.IsCMField K]

/-- Evaluation at the chosen primitive root gives the literal ambient
diagonal unit constructed in `VandiverDiagonalUnits`. -/
theorem eval₂_diagonalVandiverPolynomial587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) (i : SourceIndex 587) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (diagonalVandiverPolynomial587 i) =
      (diagonalVandiverUnit587 hzeta i : 𝓞 K) := by
  rw [diagonalVandiverPolynomial587, Polynomial.eval₂_finsetProd,
    diagonalVandiverUnit587]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval₂_pow]
  congr 1
  exact eval₂_basicVandiverPolynomial587 hzeta j

/-! ## Polynomials attached to an arbitrary integer exponent relation -/

/-- The positive polynomial attached to natural exponents `b`.  The outer
factor `586 = 587 - 1` is exactly Vandiver's factor in equation (3b). -/
def positiveRelationPolynomial587
    (b : SourceIndex 587 → ℕ) : Polynomial ℤ :=
  ∏ i, diagonalVandiverPolynomial587 i ^ (586 * b i)

/-- Exponential substitution commutes with the positive relation product. -/
theorem polynomialExp587_positiveRelationPolynomial587
    (b : SourceIndex 587 → ℕ) :
    polynomialExp587 (positiveRelationPolynomial587 b) =
      ∏ i,
        Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative.integralDiagonalSeries587 i ^
          (586 * b i) := by
  rw [positiveRelationPolynomial587, polynomialExp587,
    Polynomial.eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow]
  congr 1
  exact polynomialExp587_diagonalVandiverPolynomial587 i

/-- Every diagonal series has nonzero constant coefficient. -/
theorem constantCoeff_integralDiagonalSeries587_ne_zero
    (i : SourceIndex 587) :
    PowerSeries.constantCoeff
      (Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative.integralDiagonalSeries587 i) ≠
        0 := by
  rw [Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative.integralDiagonalSeries587,
    integralDiagonalExp]
  simp only [map_prod, constantCoeff_integralDiagonalFactor]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact pow_ne_zero _ (by norm_num)

/-- The logarithmic derivative of a positive polynomial product is the
expected natural-exponent sum. -/
theorem logarithmicDerivative_positiveRelationPolynomial587
    (b : SourceIndex 587 → ℕ) :
    logarithmicDerivative
        (polynomialExp587 (positiveRelationPolynomial587 b)) =
      ∑ i, PowerSeries.C ((586 * b i : ℕ) : ℚ) *
        logarithmicDerivative
          (Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative.integralDiagonalSeries587 i) := by
  rw [polynomialExp587_positiveRelationPolynomial587 b]
  rw [logarithmicDerivative_prod]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [logarithmicDerivative_pow]
    exact constantCoeff_integralDiagonalSeries587_ne_zero i
  · intro i hi
    apply constantCoeff_pow_ne_zero
    exact constantCoeff_integralDiagonalSeries587_ne_zero i

/-- High derivatives of the preceding identity, in the exact normalization
used by `relationDerivative587`. -/
theorem formalDerivativeAtZero_positiveRelationPolynomial587
    (b : SourceIndex 587 → ℕ) (k : SourceIndex 587) :
    formalDerivativeAtZero
      (Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative.sourceDerivativeOrder587 k)
      (logarithmicDerivative
        (polynomialExp587 (positiveRelationPolynomial587 b))) =
      ∑ i, ((586 * b i : ℕ) : ℚ) *
        formalDerivativeAtZero
          (Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative.sourceDerivativeOrder587 k)
          (logarithmicDerivative
            (Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative.integralDiagonalSeries587 i)) := by
  rw [logarithmicDerivative_positiveRelationPolynomial587 b,
    formalDerivativeAtZero_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [formalDerivativeAtZero_C_mul]

/-- Clearing negative exponents does not change the source derivative:
the integer relation derivative is the logarithmic derivative of the
positive numerator minus that of the positive denominator. -/
theorem relationDerivative587_eq_positive_sub_negative
    (a : SourceIndex 587 → ℤ) (k : SourceIndex 587) :
    Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative.relationDerivative587 a k =
      formalDerivativeAtZero
        (Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative.sourceDerivativeOrder587 k)
        (logarithmicDerivative
          (polynomialExp587
            (positiveRelationPolynomial587 (fun i ↦ (a i).toNat)))) -
      formalDerivativeAtZero
        (Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative.sourceDerivativeOrder587 k)
        (logarithmicDerivative
          (polynomialExp587
            (positiveRelationPolynomial587
              (fun i ↦ (-a i).toNat)))) := by
  rw [formalDerivativeAtZero_positiveRelationPolynomial587,
    formalDerivativeAtZero_positiveRelationPolynomial587]
  rw [Fermat.FiveHundredEightySeven.VandiverDiagonalDerivative.relationDerivative587,
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
    (E : SourceIndex 587 → G) (t : ℕ)
    (a : SourceIndex 587 → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (∏ i, E i ^ (a i).toNat) =
      u ^ t * ∏ i, E i ^ (-a i).toNat := by
  rw [hrel, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact (zpow_mul_pow_negToNat_eq_pow_toNat (E i) (a i)).symm

/-- The ambient unit represented by the unscaled positive exponent
product.  Its 586th power is the value of
`positiveRelationPolynomial587`. -/
def positiveRelationUnit587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587)
    (b : SourceIndex 587 → ℕ) : (𝓞 K)ˣ :=
  ∏ i, diagonalVandiverUnit587 hzeta i ^ b i

/-- Evaluation of a positive relation polynomial is the 586th power of
its corresponding unit product. -/
theorem eval₂_positiveRelationPolynomial587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587)
    (b : SourceIndex 587 → ℕ) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial587 b) =
      (positiveRelationUnit587 hzeta b ^ 586 : 𝓞 K) := by
  rw [positiveRelationPolynomial587, Polynomial.eval₂_finsetProd,
    positiveRelationUnit587, Units.coe_prod]
  simp_rw [Units.val_pow_eq_pow_val]
  rw [← Finset.prod_pow Finset.univ 586
    (fun i ↦ (diagonalVandiverUnit587 hzeta i : 𝓞 K) ^ b i)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow, eval₂_diagonalVandiverPolynomial587,
    ← pow_mul]
  congr 1
  omega

/-- An actual unit relation gives the exact denominator-cleared evaluation
identity to which the cyclotomic polynomial remainder theorem is applied. -/
theorem eval₂_positive_relation_of_relation {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587)
    (u : (𝓞 K)ˣ) (t : ℕ) (a : SourceIndex 587 → ℤ)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit587 hzeta i ^ a i) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial587 (fun i ↦ (a i).toNat)) =
      (u : 𝓞 K) ^ (586 * t) *
        Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
          (positiveRelationPolynomial587 (fun i ↦ (-a i).toNat)) := by
  rw [eval₂_positiveRelationPolynomial587,
    eval₂_positiveRelationPolynomial587]
  have hpos := positive_relation_of_zpow_relation
    (E := diagonalVandiverUnit587 hzeta) t a hrel
  have hpow := congrArg (fun x : (𝓞 K)ˣ ↦ x ^ 586) hpos
  have hval := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hpow
  simpa only [positiveRelationUnit587, Units.val_pow_eq_pow_val,
    Units.val_mul, mul_pow, ← pow_mul, Nat.mul_comm] using hval

end

end Fermat.FiveHundredEightySeven.VandiverPolynomialUnits
