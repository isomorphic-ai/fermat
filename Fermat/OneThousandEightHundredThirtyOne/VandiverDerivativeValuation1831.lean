import Fermat.Irregular.VandiverDerivativeValuationPrime
import Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalArithmetic1831

/-!
# The valuation step in Vandiver's diagonal calculation at 1831

The finite diagonal sum leaves the exact coefficient `7946939700` and
Teichmüller root `4746`.  Both are `1831`-adic units.  The generic
valuation theorem therefore converts divisibility of the logarithmic
derivative by `1831²` into divisibility of the corresponding relation
exponent times the Bernoulli numerator by `1831³`.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.VandiverDerivativeValuation

open Fermat.Irregular
open Fermat.Irregular.BernoulliData
open Fermat.Irregular.VandiverDerivativeValuationPrime
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalArithmetic

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

/-- Modern Bernoulli index attached to the `k`th source unit. -/
def derivativeBernoulliIndex1831 (k : SourceIndex 1831) : ℕ :=
  (2 * sourceNumber k) * 1831

/-- The exact diagonal coefficient supplied by the positive character
calculation. -/
def diagonalDerivativeFactor1831 (k : SourceIndex 1831) : ℚ :=
  (7946939700 : ℚ) *
    (bernoulli (derivativeBernoulliIndex1831 k) /
      (derivativeBernoulliIndex1831 k : ℚ)) *
    ((4746 : ℚ) ^ derivativeBernoulliIndex1831 k - 1)

theorem derivativeBernoulliIndex1831_even (k : SourceIndex 1831) :
    Even (derivativeBernoulliIndex1831 k) := by
  simpa only [derivativeBernoulliIndex1831,
    derivativeBernoulliIndex] using
    derivativeBernoulliIndex_even (p := 1831) k

theorem oneThousandEightHundredThirty_not_dvd_derivativeBernoulliIndex1831
    (k : SourceIndex 1831) :
    ¬1830 ∣ derivativeBernoulliIndex1831 k := by
  simpa only [derivativeBernoulliIndex1831,
    derivativeBernoulliIndex] using
    p_sub_one_not_dvd_derivativeBernoulliIndex
      (p := 1831) (r := 915) (by norm_num) k

/-- Von Staudt--Clausen supplies the denominator control. -/
theorem bernoulli_denominatorPrimeTo1831 (k : SourceIndex 1831) :
    DenominatorPrimeTo 1831
      (bernoulli (derivativeBernoulliIndex1831 k)) := by
  simpa only [derivativeBernoulliIndex1831,
    derivativeBernoulliIndex] using
    bernoulli_denominatorPrimeTo
      (p := 1831) (r := 915) (by norm_num) k

theorem oneThousandEightHundredThirtyOne_not_dvd_two_mul_sourceNumber
    (k : SourceIndex 1831) :
    ¬1831 ∣ 2 * sourceNumber k := by
  exact p_not_dvd_two_mul_sourceNumber
    (p := 1831) (r := 915) (by norm_num) k

theorem oneThousandEightHundredThirtyOne_not_dvd_rootFactor1831
    (k : SourceIndex 1831) :
    ¬1831 ∣ 4746 ^ derivativeBernoulliIndex1831 k - 1 := by
  simpa only [derivativeBernoulliIndex1831,
    derivativeBernoulliIndex] using
    p_not_dvd_rootFactor
      (p := 1831) (r := 915) (t := 4746) (by norm_num)
      teichmullerRoot1831_isPrimitive k

/-- Exact valuation of the diagonal factor multiplied by a nonzero
relation exponent. -/
theorem padicValRat_intCast_mul_diagonalDerivativeFactor1831
    (k : SourceIndex 1831) (a : ℤ) (ha : a ≠ 0)
    (hB : bernoulli (derivativeBernoulliIndex1831 k) ≠ 0) :
    padicValRat 1831 ((a : ℚ) * diagonalDerivativeFactor1831 k) =
      padicValInt 1831
          (a * (bernoulli (derivativeBernoulliIndex1831 k)).num) - 1 := by
  convert
    padicValRat_intCast_mul_diagonalDerivativeFactor
      (p := 1831) (r := 915) (t := 4746)
      (by norm_num) teichmullerRoot1831_isPrimitive
      7946939700 (by norm_num) k a ha hB using 1

/-- A diagonal logarithmic derivative divisible by `1831²` forces the
source cube congruence. -/
theorem cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
    (k : SourceIndex 1831) (a : ℤ)
    (hderivative : PadicValAtLeast 1831 2
      ((a : ℚ) * diagonalDerivativeFactor1831 k)) :
    (1831 : ℤ) ^ 3 ∣
      a * vandiverBernoulliNumerator 1831 k := by
  apply
    Fermat.Irregular.VandiverDerivativeValuationPrime.cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
      (p := 1831) (r := 915) (t := 4746)
      (by norm_num) teichmullerRoot1831_isPrimitive
      7946939700 (by norm_num) k a
  simpa [diagonalDerivativeFactor1831, derivativeBernoulliIndex1831,
    diagonalDerivativeFactor, derivativeBernoulliIndex] using hderivative

end Fermat.OneThousandEightHundredThirtyOne.VandiverDerivativeValuation
