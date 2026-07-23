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

end

end Fermat.ThirtySeven.VandiverPolynomialUnits
