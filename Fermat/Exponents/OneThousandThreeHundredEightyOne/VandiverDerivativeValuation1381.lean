import Fermat.Descent.Irregular.VandiverDerivativeValuationPrime
import Fermat.Exponents.OneThousandThreeHundredEightyOne.VandiverDiagonalArithmetic1381

/-!
# The valuation step in Vandiver's diagonal calculation at 1381

The finite diagonal sum leaves the exact coefficient `621786600` and
Teichmüller root `653`.  Both are `1381`-adic units.  The generic
valuation theorem therefore converts divisibility of the logarithmic
derivative by `1381²` into divisibility of the corresponding relation
exponent times the Bernoulli numerator by `1381³`.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverDerivativeValuation

open Fermat.Irregular
open Fermat.Irregular.BernoulliData
open Fermat.Irregular.VandiverDerivativeValuationPrime
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalArithmetic

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

/-- Modern Bernoulli index attached to the `k`th source unit. -/
def derivativeBernoulliIndex1381 (k : SourceIndex 1381) : ℕ :=
  (2 * sourceNumber k) * 1381

/-- The exact diagonal coefficient supplied by the positive character
calculation. -/
def diagonalDerivativeFactor1381 (k : SourceIndex 1381) : ℚ :=
  (621786600 : ℚ) *
    (bernoulli (derivativeBernoulliIndex1381 k) /
      (derivativeBernoulliIndex1381 k : ℚ)) *
    ((653 : ℚ) ^ derivativeBernoulliIndex1381 k - 1)

theorem derivativeBernoulliIndex1381_even (k : SourceIndex 1381) :
    Even (derivativeBernoulliIndex1381 k) := by
  simpa only [derivativeBernoulliIndex1381,
    derivativeBernoulliIndex] using
    derivativeBernoulliIndex_even (p := 1381) k

theorem oneThousandThreeHundredEighty_not_dvd_derivativeBernoulliIndex1381
    (k : SourceIndex 1381) :
    ¬1380 ∣ derivativeBernoulliIndex1381 k := by
  simpa only [derivativeBernoulliIndex1381,
    derivativeBernoulliIndex] using
    p_sub_one_not_dvd_derivativeBernoulliIndex
      (p := 1381) (r := 690) (by norm_num) k

/-- Von Staudt--Clausen supplies the denominator control. -/
theorem bernoulli_denominatorPrimeTo1381 (k : SourceIndex 1381) :
    DenominatorPrimeTo 1381
      (bernoulli (derivativeBernoulliIndex1381 k)) := by
  simpa only [derivativeBernoulliIndex1381,
    derivativeBernoulliIndex] using
    bernoulli_denominatorPrimeTo
      (p := 1381) (r := 690) (by norm_num) k

theorem oneThousandThreeHundredEightyOne_not_dvd_two_mul_sourceNumber
    (k : SourceIndex 1381) :
    ¬1381 ∣ 2 * sourceNumber k := by
  exact p_not_dvd_two_mul_sourceNumber
    (p := 1381) (r := 690) (by norm_num) k

theorem oneThousandThreeHundredEightyOne_not_dvd_rootFactor1381
    (k : SourceIndex 1381) :
    ¬1381 ∣ 653 ^ derivativeBernoulliIndex1381 k - 1 := by
  simpa only [derivativeBernoulliIndex1381,
    derivativeBernoulliIndex] using
    p_not_dvd_rootFactor
      (p := 1381) (r := 690) (t := 653) (by norm_num)
      teichmullerRoot1381_isPrimitive k

/-- Exact valuation of the diagonal factor multiplied by a nonzero
relation exponent. -/
theorem padicValRat_intCast_mul_diagonalDerivativeFactor1381
    (k : SourceIndex 1381) (a : ℤ) (ha : a ≠ 0)
    (hB : bernoulli (derivativeBernoulliIndex1381 k) ≠ 0) :
    padicValRat 1381 ((a : ℚ) * diagonalDerivativeFactor1381 k) =
      padicValInt 1381
          (a * (bernoulli (derivativeBernoulliIndex1381 k)).num) - 1 := by
  convert
    padicValRat_intCast_mul_diagonalDerivativeFactor
      (p := 1381) (r := 690) (t := 653)
      (by norm_num) teichmullerRoot1381_isPrimitive
      621786600 (by norm_num) k a ha hB using 1

/-- A diagonal logarithmic derivative divisible by `1381²` forces the
source cube congruence. -/
theorem cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
    (k : SourceIndex 1381) (a : ℤ)
    (hderivative : PadicValAtLeast 1381 2
      ((a : ℚ) * diagonalDerivativeFactor1381 k)) :
    (1381 : ℤ) ^ 3 ∣
      a * vandiverBernoulliNumerator 1381 k := by
  apply
    Fermat.Irregular.VandiverDerivativeValuationPrime.cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
      (p := 1381) (r := 690) (t := 653)
      (by norm_num) teichmullerRoot1381_isPrimitive
      621786600 (by norm_num) k a
  simpa [diagonalDerivativeFactor1381, derivativeBernoulliIndex1381,
    diagonalDerivativeFactor, derivativeBernoulliIndex] using hderivative

end Fermat.OneThousandThreeHundredEightyOne.VandiverDerivativeValuation
