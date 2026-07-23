import Fermat.ThirtySeven.VandiverDiagonalDerivative
import Fermat.ThirtySeven.VandiverDiagonalUnits

/-!
# Vandiver's integral unit polynomials at exponent 37

This file identifies the two incarnations of the diagonal units used in
Vandiver's Lemma II.

For a positive integer `s`, put

`epsilon_s(W) = W^(18*s) * (1 + W^s + ... + W^(75*s))`.

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

namespace Fermat.ThirtySeven.VandiverPolynomialUnits

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.ThirtySeven.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

set_option maxRecDepth 100000

/-- Formal substitution of `exp V` into an integer polynomial. -/
def polynomialExp37 (P : Polynomial ℤ) : PowerSeries ℚ :=
  Polynomial.eval₂ (algebraMap ℤ (PowerSeries ℚ))
    (PowerSeries.exp ℚ) P

/-- Vandiver's basic integral polynomial
`W^(18*s) * (1 + W^s + ... + W^(75*s))`. -/
def basicVandiverPolynomial37 (s : ℕ) : Polynomial ℤ :=
  Polynomial.X ^ (18 * s) *
    ∑ j ∈ Finset.range 76, Polynomial.X ^ (s * j)

/-- Substitution `W = exp V` turns the basic integral polynomial into
the normalized geometric exponential used in the derivative calculation. -/
theorem polynomialExp37_basicVandiverPolynomial37 (s : ℕ) :
    polynomialExp37 (basicVandiverPolynomial37 s) =
      normalizedGeomExp 76 18 s := by
  rw [polynomialExp37, basicVandiverPolynomial37, Polynomial.eval₂_mul,
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
theorem eval₂_basicVandiverPolynomial37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37)
    (j : VandiverFactorIndex37) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (basicVandiverPolynomial37 (conjugateExponent37 j)) =
      (basicVandiverUnit37 hzeta j : 𝓞 K) := by
  rw [basicVandiverUnit37,
    Fermat.Irregular.CircularUnitFamily.normalizedCircularUnit_val]
  rw [conjugate_toInteger (hzeta := hzeta) j]
  simp only [basicVandiverPolynomial37, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_finsetSum]
  congr 1 <;> simp only [← pow_mul] <;> ring_nf

/-- Vandiver's positive integral polynomial representing the `i`th
diagonal unit. -/
def diagonalVandiverPolynomial37
    (i : SourceIndex 37) : Polynomial ℤ :=
  ∏ j : VandiverFactorIndex37,
    basicVandiverPolynomial37 (conjugateExponent37 j) ^
      diagonalWeight37 i j

/-- The exponential substitution of the actual diagonal polynomial is
definitionally the formal diagonal series used in the derivative theorem. -/
theorem polynomialExp37_diagonalVandiverPolynomial37
    (i : SourceIndex 37) :
    polynomialExp37 (diagonalVandiverPolynomial37 i) =
      Fermat.ThirtySeven.VandiverDiagonalDerivative.integralDiagonalSeries37 i := by
  rw [diagonalVandiverPolynomial37, polynomialExp37,
    Polynomial.eval₂_finsetProd]
  simp_rw [Polynomial.eval₂_pow]
  rw [Fermat.ThirtySeven.VandiverDiagonalDerivative.integralDiagonalSeries37,
    integralDiagonalExp]
  norm_num
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [dif_pos hj]
  simp only [integralDiagonalFactor, diagonalWeight37,
    conjugateExponent37, sourceNumber]
  change
    (polynomialExp37 (basicVandiverPolynomial37 (76 ^ j))) ^
          integralDiagonalWeight 37 76 (i.val + 1) j =
      normalizedGeomExp 76 18 (76 ^ j) ^
          integralDiagonalWeight 37 76 (i.val + 1) j
  rw [polynomialExp37_basicVandiverPolynomial37]

variable [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-- Evaluation at the chosen primitive root gives the literal ambient
diagonal unit constructed in `VandiverDiagonalUnits`. -/
theorem eval₂_diagonalVandiverPolynomial37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (i : SourceIndex 37) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (diagonalVandiverPolynomial37 i) =
      (diagonalVandiverUnit37 hzeta i : 𝓞 K) := by
  rw [diagonalVandiverPolynomial37, Polynomial.eval₂_finsetProd,
    diagonalVandiverUnit37]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval₂_pow]
  congr 1
  exact eval₂_basicVandiverPolynomial37 hzeta j

/-! ## Polynomials attached to an arbitrary integer exponent relation -/

/-- The positive polynomial attached to natural exponents `b`.  The outer
factor `36 = 37 - 1` is exactly Vandiver's factor in equation (3b). -/
def positiveRelationPolynomial37
    (b : SourceIndex 37 → ℕ) : Polynomial ℤ :=
  ∏ i, diagonalVandiverPolynomial37 i ^ (36 * b i)

/-- Exponential substitution commutes with the positive relation product. -/
theorem polynomialExp37_positiveRelationPolynomial37
    (b : SourceIndex 37 → ℕ) :
    polynomialExp37 (positiveRelationPolynomial37 b) =
      ∏ i,
        Fermat.ThirtySeven.VandiverDiagonalDerivative.integralDiagonalSeries37 i ^
          (36 * b i) := by
  rw [positiveRelationPolynomial37, polynomialExp37,
    Polynomial.eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow]
  congr 1
  exact polynomialExp37_diagonalVandiverPolynomial37 i

/-- Every diagonal series has nonzero constant coefficient. -/
theorem constantCoeff_integralDiagonalSeries37_ne_zero
    (i : SourceIndex 37) :
    PowerSeries.constantCoeff
      (Fermat.ThirtySeven.VandiverDiagonalDerivative.integralDiagonalSeries37 i) ≠
        0 := by
  rw [Fermat.ThirtySeven.VandiverDiagonalDerivative.integralDiagonalSeries37,
    integralDiagonalExp]
  simp only [map_prod, constantCoeff_integralDiagonalFactor]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact pow_ne_zero _ (by norm_num)

/-- The logarithmic derivative of a positive polynomial product is the
expected natural-exponent sum. -/
theorem logarithmicDerivative_positiveRelationPolynomial37
    (b : SourceIndex 37 → ℕ) :
    logarithmicDerivative
        (polynomialExp37 (positiveRelationPolynomial37 b)) =
      ∑ i, PowerSeries.C ((36 * b i : ℕ) : ℚ) *
        logarithmicDerivative
          (Fermat.ThirtySeven.VandiverDiagonalDerivative.integralDiagonalSeries37 i) := by
  rw [polynomialExp37_positiveRelationPolynomial37 b]
  rw [logarithmicDerivative_prod]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [logarithmicDerivative_pow]
    exact constantCoeff_integralDiagonalSeries37_ne_zero i
  · intro i hi
    apply constantCoeff_pow_ne_zero
    exact constantCoeff_integralDiagonalSeries37_ne_zero i

/-- High derivatives of the preceding identity, in the exact normalization
used by `relationDerivative37`. -/
theorem formalDerivativeAtZero_positiveRelationPolynomial37
    (b : SourceIndex 37 → ℕ) (k : SourceIndex 37) :
    formalDerivativeAtZero
      (Fermat.ThirtySeven.VandiverDiagonalDerivative.sourceDerivativeOrder37 k)
      (logarithmicDerivative
        (polynomialExp37 (positiveRelationPolynomial37 b))) =
      ∑ i, ((36 * b i : ℕ) : ℚ) *
        formalDerivativeAtZero
          (Fermat.ThirtySeven.VandiverDiagonalDerivative.sourceDerivativeOrder37 k)
          (logarithmicDerivative
            (Fermat.ThirtySeven.VandiverDiagonalDerivative.integralDiagonalSeries37 i)) := by
  rw [logarithmicDerivative_positiveRelationPolynomial37 b,
    formalDerivativeAtZero_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [formalDerivativeAtZero_C_mul]

/-- Clearing negative exponents does not change the source derivative:
the integer relation derivative is the logarithmic derivative of the
positive numerator minus that of the positive denominator. -/
theorem relationDerivative37_eq_positive_sub_negative
    (a : SourceIndex 37 → ℤ) (k : SourceIndex 37) :
    Fermat.ThirtySeven.VandiverDiagonalDerivative.relationDerivative37 a k =
      formalDerivativeAtZero
        (Fermat.ThirtySeven.VandiverDiagonalDerivative.sourceDerivativeOrder37 k)
        (logarithmicDerivative
          (polynomialExp37
            (positiveRelationPolynomial37 (fun i ↦ (a i).toNat)))) -
      formalDerivativeAtZero
        (Fermat.ThirtySeven.VandiverDiagonalDerivative.sourceDerivativeOrder37 k)
        (logarithmicDerivative
          (polynomialExp37
            (positiveRelationPolynomial37
              (fun i ↦ (-a i).toNat)))) := by
  rw [formalDerivativeAtZero_positiveRelationPolynomial37,
    formalDerivativeAtZero_positiveRelationPolynomial37]
  rw [Fermat.ThirtySeven.VandiverDiagonalDerivative.relationDerivative37,
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
    (E : SourceIndex 37 → G) (t : ℕ)
    (a : SourceIndex 37 → ℤ)
    (hrel : u ^ t = ∏ i, E i ^ a i) :
    (∏ i, E i ^ (a i).toNat) =
      u ^ t * ∏ i, E i ^ (-a i).toNat := by
  rw [hrel, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact (zpow_mul_pow_negToNat_eq_pow_toNat (E i) (a i)).symm

/-- The ambient unit represented by the unscaled positive exponent
product.  Its 36th power is the value of
`positiveRelationPolynomial37`. -/
def positiveRelationUnit37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37)
    (b : SourceIndex 37 → ℕ) : (𝓞 K)ˣ :=
  ∏ i, diagonalVandiverUnit37 hzeta i ^ b i

/-- Evaluation of a positive relation polynomial is the 36th power of
its corresponding unit product. -/
theorem eval₂_positiveRelationPolynomial37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37)
    (b : SourceIndex 37 → ℕ) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial37 b) =
      (positiveRelationUnit37 hzeta b ^ 36 : 𝓞 K) := by
  rw [positiveRelationPolynomial37, Polynomial.eval₂_finsetProd,
    positiveRelationUnit37, Units.coe_prod]
  simp_rw [Units.val_pow_eq_pow_val]
  rw [← Finset.prod_pow Finset.univ 36
    (fun i ↦ (diagonalVandiverUnit37 hzeta i : 𝓞 K) ^ b i)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval₂_pow, eval₂_diagonalVandiverPolynomial37,
    ← pow_mul]
  congr 1
  omega

/-- An actual unit relation gives the exact denominator-cleared evaluation
identity to which the cyclotomic polynomial remainder theorem is applied. -/
theorem eval₂_positive_relation_of_relation {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37)
    (u : (𝓞 K)ˣ) (t : ℕ) (a : SourceIndex 37 → ℤ)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit37 hzeta i ^ a i) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (positiveRelationPolynomial37 (fun i ↦ (a i).toNat)) =
      (u : 𝓞 K) ^ (36 * t) *
        Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
          (positiveRelationPolynomial37 (fun i ↦ (-a i).toNat)) := by
  rw [eval₂_positiveRelationPolynomial37,
    eval₂_positiveRelationPolynomial37]
  have hpos := positive_relation_of_zpow_relation
    (E := diagonalVandiverUnit37 hzeta) t a hrel
  have hpow := congrArg (fun x : (𝓞 K)ˣ ↦ x ^ 36) hpos
  have hval := congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hpow
  simpa only [positiveRelationUnit37, Units.val_pow_eq_pow_val,
    Units.val_mul, mul_pow, ← pow_mul, Nat.mul_comm] using hval

end

end Fermat.ThirtySeven.VandiverPolynomialUnits
