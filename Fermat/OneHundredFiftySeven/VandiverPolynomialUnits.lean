import Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative157
import Fermat.OneHundredFiftySeven.VandiverDiagonalUnits157

/-!
# Vandiver's integral unit polynomials at exponent 157

This file identifies the two incarnations of the diagonal units used in
Vandiver's Lemma II.

For a positive integer `s`, put

`epsilon_s(W) = W^(123*s) * (1 + W^s + ... + W^(225*s))`.

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

namespace Fermat.OneHundredFiftySeven.VandiverPolynomialUnits

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.OneHundredFiftySeven.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 157) := ⟨by decide⟩

set_option maxRecDepth 100000

/-- Formal substitution of `exp V` into an integer polynomial. -/
def polynomialExp157 (P : Polynomial ℤ) : PowerSeries ℚ :=
  Polynomial.eval₂ (algebraMap ℤ (PowerSeries ℚ))
    (PowerSeries.exp ℚ) P

/-- Vandiver's basic integral polynomial
`W^(123*s) * (1 + W^s + ... + W^(225*s))`. -/
def basicVandiverPolynomial157 (s : ℕ) : Polynomial ℤ :=
  Polynomial.X ^ (123 * s) *
    ∑ j ∈ Finset.range 226, Polynomial.X ^ (s * j)

/-- Substitution `W = exp V` turns the basic integral polynomial into
the normalized geometric exponential used in the derivative calculation. -/
theorem polynomialExp157_basicVandiverPolynomial157 (s : ℕ) :
    polynomialExp157 (basicVandiverPolynomial157 s) =
      normalizedGeomExp 226 123 s := by
  rw [polynomialExp157, basicVandiverPolynomial157, Polynomial.eval₂_mul,
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
theorem eval₂_basicVandiverPolynomial157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157)
    (j : VandiverFactorIndex157) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (basicVandiverPolynomial157 (conjugateExponent157 j)) =
      (basicVandiverUnit157 hzeta j : 𝓞 K) := by
  rw [basicVandiverUnit157,
    Fermat.Irregular.CircularUnitFamily.normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [basicVandiverPolynomial157, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_finsetSum]
  congr 1 <;> simp only [← pow_mul] <;> ring_nf

/-- Vandiver's positive integral polynomial representing the `i`th
diagonal unit. -/
def diagonalVandiverPolynomial157
    (i : SourceIndex 157) : Polynomial ℤ :=
  ∏ j : VandiverFactorIndex157,
    basicVandiverPolynomial157 (conjugateExponent157 j) ^
      diagonalWeight157 i j

/-- The exponential substitution of the actual diagonal polynomial is
definitionally the formal diagonal series used in the derivative theorem. -/
theorem polynomialExp157_diagonalVandiverPolynomial157
    (i : SourceIndex 157) :
    polynomialExp157 (diagonalVandiverPolynomial157 i) =
      Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative.integralDiagonalSeries157 i := by
  rw [diagonalVandiverPolynomial157, polynomialExp157,
    Polynomial.eval₂_finsetProd]
  simp_rw [Polynomial.eval₂_pow]
  rw [Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative.integralDiagonalSeries157,
    integralDiagonalExp]
  norm_num
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [dif_pos hj]
  simp only [integralDiagonalFactor, diagonalWeight157,
    conjugateExponent157, sourceNumber]
  change
    (polynomialExp157 (basicVandiverPolynomial157 (226 ^ j))) ^
          integralDiagonalWeight 157 226 (i.val + 1) j =
      normalizedGeomExp 226 123 (226 ^ j) ^
          integralDiagonalWeight 157 226 (i.val + 1) j
  rw [polynomialExp157_basicVandiverPolynomial157]

variable [NumberField K] [IsCyclotomicExtension {157} ℚ K]
  [NumberField.IsCMField K]

/-- Evaluation at the chosen primitive root gives the literal ambient
diagonal unit constructed in `VandiverDiagonalUnits`. -/
theorem eval₂_diagonalVandiverPolynomial157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) (i : SourceIndex 157) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (diagonalVandiverPolynomial157 i) =
      (diagonalVandiverUnit157 hzeta i : 𝓞 K) := by
  rw [diagonalVandiverPolynomial157, Polynomial.eval₂_finsetProd,
    diagonalVandiverUnit157]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval₂_pow]
  congr 1
  exact eval₂_basicVandiverPolynomial157 hzeta j

/-! ## Polynomials attached to an arbitrary integer exponent relation -/

/-- The positive polynomial attached to natural exponents `b`.  The outer
factor `156 = 157 - 1` is exactly Vandiver's factor in equation (3b). -/
def positiveRelationPolynomial157
    (b : SourceIndex 157 → ℕ) : Polynomial ℤ :=
  ∏ i, diagonalVandiverPolynomial157 i ^ (156 * b i)

/-- Exponential substitution commutes with the positive relation product. -/
theorem polynomialExp157_positiveRelationPolynomial157
    (b : SourceIndex 157 → ℕ) :
    polynomialExp157 (positiveRelationPolynomial157 b) =
      ∏ i,
        Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative.integralDiagonalSeries157 i ^
          (156 * b i) := by
  rw [positiveRelationPolynomial157, polynomialExp157,
    Polynomial.eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow]
  congr 1
  exact polynomialExp157_diagonalVandiverPolynomial157 i

/-- Every diagonal series has nonzero constant coefficient. -/
theorem constantCoeff_integralDiagonalSeries157_ne_zero
    (i : SourceIndex 157) :
    PowerSeries.constantCoeff
      (Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative.integralDiagonalSeries157 i) ≠
        0 := by
  rw [Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative.integralDiagonalSeries157,
    integralDiagonalExp]
  simp only [map_prod, constantCoeff_integralDiagonalFactor]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact pow_ne_zero _ (by norm_num)

/-- The logarithmic derivative of a positive polynomial product is the
expected natural-exponent sum. -/
theorem logarithmicDerivative_positiveRelationPolynomial157
    (b : SourceIndex 157 → ℕ) :
    logarithmicDerivative
        (polynomialExp157 (positiveRelationPolynomial157 b)) =
      ∑ i, PowerSeries.C ((156 * b i : ℕ) : ℚ) *
        logarithmicDerivative
          (Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative.integralDiagonalSeries157 i) := by
  rw [polynomialExp157_positiveRelationPolynomial157 b]
  rw [logarithmicDerivative_prod]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [logarithmicDerivative_pow]
    exact constantCoeff_integralDiagonalSeries157_ne_zero i
  · intro i hi
    apply constantCoeff_pow_ne_zero
    exact constantCoeff_integralDiagonalSeries157_ne_zero i

/-- High derivatives of the preceding identity, in the exact normalization
used by `relationDerivative157`. -/
theorem formalDerivativeAtZero_positiveRelationPolynomial157
    (b : SourceIndex 157 → ℕ) (k : SourceIndex 157) :
    formalDerivativeAtZero
      (Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative.sourceDerivativeOrder157 k)
      (logarithmicDerivative
        (polynomialExp157 (positiveRelationPolynomial157 b))) =
      ∑ i, ((156 * b i : ℕ) : ℚ) *
        formalDerivativeAtZero
          (Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative.sourceDerivativeOrder157 k)
          (logarithmicDerivative
            (Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative.integralDiagonalSeries157 i)) := by
  rw [logarithmicDerivative_positiveRelationPolynomial157 b,
    formalDerivativeAtZero_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [formalDerivativeAtZero_C_mul]

/-- Clearing negative exponents does not change the source derivative:
the integer relation derivative is the logarithmic derivative of the
positive numerator minus that of the positive denominator. -/
theorem relationDerivative157_eq_positive_sub_negative
    (a : SourceIndex 157 → ℤ) (k : SourceIndex 157) :
    Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative.relationDerivative157 a k =
      formalDerivativeAtZero
        (Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative.sourceDerivativeOrder157 k)
        (logarithmicDerivative
          (polynomialExp157
            (positiveRelationPolynomial157 (fun i ↦ (a i).toNat)))) -
      formalDerivativeAtZero
        (Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative.sourceDerivativeOrder157 k)
        (logarithmicDerivative
          (polynomialExp157
            (positiveRelationPolynomial157
              (fun i ↦ (-a i).toNat)))) := by
  rw [formalDerivativeAtZero_positiveRelationPolynomial157,
    formalDerivativeAtZero_positiveRelationPolynomial157]
  rw [Fermat.OneHundredFiftySeven.VandiverDiagonalDerivative.relationDerivative157,
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
    (E : SourceIndex 157 → G) (t : ℕ)
    (a : SourceIndex 157 → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (∏ i, E i ^ (a i).toNat) =
      u ^ t * ∏ i, E i ^ (-a i).toNat := by
  rw [hrel, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact (zpow_mul_pow_negToNat_eq_pow_toNat (E i) (a i)).symm

/-- The ambient unit represented by the unscaled positive exponent
product.  Its 66th power is the value of
`positiveRelationPolynomial157`. -/
def positiveRelationUnit157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157)
    (b : SourceIndex 157 → ℕ) : (𝓞 K)ˣ :=
  ∏ i, diagonalVandiverUnit157 hzeta i ^ b i

/-- Evaluation of a positive relation polynomial is the 66th power of
its corresponding unit product. -/
theorem eval₂_positiveRelationPolynomial157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157)
    (b : SourceIndex 157 → ℕ) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial157 b) =
      (positiveRelationUnit157 hzeta b ^ 156 : 𝓞 K) := by
  rw [positiveRelationPolynomial157, Polynomial.eval₂_finsetProd,
    positiveRelationUnit157, Units.coe_prod]
  simp_rw [Units.val_pow_eq_pow_val]
  rw [← Finset.prod_pow Finset.univ 156
    (fun i ↦ (diagonalVandiverUnit157 hzeta i : 𝓞 K) ^ b i)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow, eval₂_diagonalVandiverPolynomial157,
    ← pow_mul]
  congr 1
  omega

/-- An actual unit relation gives the exact denominator-cleared evaluation
identity to which the cyclotomic polynomial remainder theorem is applied. -/
theorem eval₂_positive_relation_of_relation {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157)
    (u : (𝓞 K)ˣ) (t : ℕ) (a : SourceIndex 157 → ℤ)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit157 hzeta i ^ a i) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial157 (fun i ↦ (a i).toNat)) =
      (u : 𝓞 K) ^ (156 * t) *
        Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
          (positiveRelationPolynomial157 (fun i ↦ (-a i).toNat)) := by
  rw [eval₂_positiveRelationPolynomial157,
    eval₂_positiveRelationPolynomial157]
  have hpos := positive_relation_of_zpow_relation
    (E := diagonalVandiverUnit157 hzeta) t a hrel
  have hpow := congrArg (fun x : (𝓞 K)ˣ ↦ x ^ 156) hpos
  have hval := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hpow
  simpa only [positiveRelationUnit157, Units.val_pow_eq_pow_val,
    Units.val_mul, mul_pow, ← pow_mul, Nat.mul_comm] using hval

end

end Fermat.OneHundredFiftySeven.VandiverPolynomialUnits
