import Fermat.Exponents.TwelveThousandSixHundredThirteen.VandiverDiagonalUnits12613

/-!
# Vandiver's integral unit polynomials at exponent 12613

This file identifies the polynomial and real-unit incarnations of the new
diagonal family.  For a positive integer `s`, its basic polynomial is

`epsilon_s(W) = W^(9283*s) * (1 + W^s + ... + W^(6660*s))`.

At a primitive `12613`th root this is the literal normalized circular unit
from `VandiverDiagonalUnits12613`.  Under the formal substitution
`W = exp V`, it is the normalized geometric exponential with intrinsic
parameters `tau = 6661` and `e = 9283`.
-/

open scoped BigOperators NumberField

namespace Fermat.TwelveThousandSixHundredThirteen.VandiverPolynomialUnits

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular.VandiverDiagonalLogDerivative
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.TwelveThousandSixHundredThirteen.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 12613) := ⟨by norm_num⟩

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Formal substitution of `exp V` into an integer polynomial. -/
def polynomialExp12613 (P : Polynomial ℤ) : PowerSeries ℚ :=
  Polynomial.eval₂ (algebraMap ℤ (PowerSeries ℚ))
    (PowerSeries.exp ℚ) P

/-- Vandiver's basic integral polynomial
`W^(9283*s) * (1 + W^s + ... + W^(6660*s))`. -/
def basicVandiverPolynomial12613 (s : ℕ) : Polynomial ℤ :=
  Polynomial.X ^ (normalizationExponent12613 * s) *
    ∑ j ∈ Finset.range teichmullerRoot12613,
      Polynomial.X ^ (s * j)

/-- Substitution `W = exp V` turns the basic integral polynomial into the
normalized geometric exponential. -/
theorem polynomialExp12613_basicVandiverPolynomial12613 (s : ℕ) :
    polynomialExp12613 (basicVandiverPolynomial12613 s) =
      normalizedGeomExp teichmullerRoot12613
        normalizationExponent12613 s := by
  rw [polynomialExp12613, basicVandiverPolynomial12613,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_finsetSum]
  simp_rw [Polynomial.eval₂_pow, Polynomial.eval₂_X]
  rw [normalizedGeomExp]
  congr 1
  rw [Fermat.Irregular.VandiverPowerSeriesLog.geomExp, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_pow, ← PowerSeries.exp_pow_eq_rescale_exp (A := ℚ) s,
    ← pow_mul]

variable {K : Type*} [Field K]

/-- At the integral lift of `zeta`, the basic polynomial is the actual
basic Vandiver unit. -/
theorem eval₂_basicVandiverPolynomial12613 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 12613)
    (j : VandiverFactorIndex12613) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (basicVandiverPolynomial12613 (conjugateExponent12613 j)) =
      (basicVandiverUnit12613 hzeta j : 𝓞 K) := by
  rw [basicVandiverUnit12613,
    Fermat.Irregular.CircularUnitFamily.normalizedCircularUnit_val]
  rw [conjugate_toInteger12613 (hzeta := hzeta) j]
  simp only [basicVandiverPolynomial12613, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_finsetSum]
  congr 1
  all_goals simp only [← pow_mul]
  all_goals ring_nf

/-- The formal diagonal series represented by the integral polynomial. -/
def integralDiagonalSeries12613
    (i : SourceIndex 12613) : PowerSeries ℚ :=
  integralDiagonalExp 12613 teichmullerRoot12613
    normalizationExponent12613 (sourceNumber i)

/-- Vandiver's positive integral polynomial representing the `i`th
diagonal unit. -/
def diagonalVandiverPolynomial12613
    (i : SourceIndex 12613) : Polynomial ℤ :=
  ∏ j : VandiverFactorIndex12613,
    basicVandiverPolynomial12613 (conjugateExponent12613 j) ^
      diagonalWeight12613 i j

/-- Exponential substitution of the diagonal polynomial is the generic
integral diagonal series with `tau = 6661` and `e = 9283`. -/
theorem polynomialExp12613_diagonalVandiverPolynomial12613
    (i : SourceIndex 12613) :
    polynomialExp12613 (diagonalVandiverPolynomial12613 i) =
      integralDiagonalSeries12613 i := by
  rw [diagonalVandiverPolynomial12613, polynomialExp12613,
    Polynomial.eval₂_finsetProd]
  simp_rw [Polynomial.eval₂_pow]
  rw [integralDiagonalSeries12613, integralDiagonalExp]
  norm_num
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [dif_pos hj]
  simp only [integralDiagonalFactor, diagonalWeight12613,
    conjugateExponent12613, sourceNumber]
  change
    (polynomialExp12613
        (basicVandiverPolynomial12613 (teichmullerRoot12613 ^ j))) ^
          integralDiagonalWeight 12613 teichmullerRoot12613
            (i.val + 1) j =
      normalizedGeomExp teichmullerRoot12613
          normalizationExponent12613 (teichmullerRoot12613 ^ j) ^
        integralDiagonalWeight 12613 teichmullerRoot12613
          (i.val + 1) j
  rw [polynomialExp12613_basicVandiverPolynomial12613]

variable [NumberField K] [IsCyclotomicExtension {12613} ℚ K]
  [NumberField.IsCMField K]

omit [NumberField K] [IsCyclotomicExtension {12613} ℚ K]
    [NumberField.IsCMField K] in
/-- Evaluation at the primitive root gives the literal ambient diagonal
unit constructed in `VandiverDiagonalUnits12613`. -/
theorem eval₂_diagonalVandiverPolynomial12613 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 12613) (i : SourceIndex 12613) :
    Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (diagonalVandiverPolynomial12613 i) =
      (diagonalVandiverUnit12613 hzeta i : 𝓞 K) := by
  rw [diagonalVandiverPolynomial12613, Polynomial.eval₂_finsetProd,
    diagonalVandiverUnit12613]
  simp only [Units.coe_prod, Units.val_pow_eq_pow_val]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval₂_pow]
  congr 1
  exact eval₂_basicVandiverPolynomial12613 hzeta j

end

end Fermat.TwelveThousandSixHundredThirteen.VandiverPolynomialUnits
