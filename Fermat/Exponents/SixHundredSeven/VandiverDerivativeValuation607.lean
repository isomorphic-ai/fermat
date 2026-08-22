import Fermat.Descent.Irregular.VandiverDerivativeValuationPrime
import Fermat.Exponents.SixHundredSeven.VandiverDiagonalArithmetic607

/-!
# The valuation step in Vandiver's diagonal calculation at 607

The finite diagonal sum leaves the exact coefficient `149281434` and
Teichmüller root `813`.  Both are `607`-adic units.  The generic
valuation theorem therefore converts divisibility of the logarithmic
derivative by `607²` into divisibility of the corresponding relation
exponent times the Bernoulli numerator by `607³`.
-/

namespace Fermat.SixHundredSeven.VandiverDerivativeValuation

open Fermat.Irregular
open Fermat.Irregular.BernoulliData
open Fermat.Irregular.VandiverDerivativeValuationPrime
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.SixHundredSeven.VandiverDiagonalArithmetic

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

/-- Modern Bernoulli index attached to the `k`th source unit. -/
def derivativeBernoulliIndex607 (k : SourceIndex 607) : ℕ :=
  (2 * sourceNumber k) * 607

/-- The exact diagonal coefficient supplied by the positive character
calculation. -/
def diagonalDerivativeFactor607 (k : SourceIndex 607) : ℚ :=
  (149281434 : ℚ) *
    (bernoulli (derivativeBernoulliIndex607 k) /
      (derivativeBernoulliIndex607 k : ℚ)) *
    ((813 : ℚ) ^ derivativeBernoulliIndex607 k - 1)

theorem derivativeBernoulliIndex607_even (k : SourceIndex 607) :
    Even (derivativeBernoulliIndex607 k) := by
  simpa only [derivativeBernoulliIndex607,
    derivativeBernoulliIndex] using
    derivativeBernoulliIndex_even (p := 607) k

theorem sixHundredSix_not_dvd_derivativeBernoulliIndex607
    (k : SourceIndex 607) :
    ¬606 ∣ derivativeBernoulliIndex607 k := by
  simpa only [derivativeBernoulliIndex607,
    derivativeBernoulliIndex] using
    p_sub_one_not_dvd_derivativeBernoulliIndex
      (p := 607) (r := 303) (by norm_num) k

/-- Von Staudt--Clausen supplies the denominator control. -/
theorem bernoulli_denominatorPrimeTo607 (k : SourceIndex 607) :
    DenominatorPrimeTo 607
      (bernoulli (derivativeBernoulliIndex607 k)) := by
  simpa only [derivativeBernoulliIndex607,
    derivativeBernoulliIndex] using
    bernoulli_denominatorPrimeTo
      (p := 607) (r := 303) (by norm_num) k

theorem sixHundredSeven_not_dvd_two_mul_sourceNumber
    (k : SourceIndex 607) :
    ¬607 ∣ 2 * sourceNumber k := by
  exact p_not_dvd_two_mul_sourceNumber
    (p := 607) (r := 303) (by norm_num) k

theorem sixHundredSeven_not_dvd_rootFactor607
    (k : SourceIndex 607) :
    ¬607 ∣ 813 ^ derivativeBernoulliIndex607 k - 1 := by
  simpa only [derivativeBernoulliIndex607,
    derivativeBernoulliIndex] using
    p_not_dvd_rootFactor
      (p := 607) (r := 303) (t := 813) (by norm_num)
      teichmullerRoot607_isPrimitive k

/-- Exact valuation of the diagonal factor multiplied by a nonzero
relation exponent. -/
theorem padicValRat_intCast_mul_diagonalDerivativeFactor607
    (k : SourceIndex 607) (a : ℤ) (ha : a ≠ 0)
    (hB : bernoulli (derivativeBernoulliIndex607 k) ≠ 0) :
    padicValRat 607 ((a : ℚ) * diagonalDerivativeFactor607 k) =
      padicValInt 607
          (a * (bernoulli (derivativeBernoulliIndex607 k)).num) - 1 := by
  convert
    padicValRat_intCast_mul_diagonalDerivativeFactor
      (p := 607) (r := 303) (t := 813)
      (by norm_num) teichmullerRoot607_isPrimitive
      149281434 (by norm_num) k a ha hB using 1

/-- A diagonal logarithmic derivative divisible by `607²` forces the
source cube congruence. -/
theorem cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
    (k : SourceIndex 607) (a : ℤ)
    (hderivative : PadicValAtLeast 607 2
      ((a : ℚ) * diagonalDerivativeFactor607 k)) :
    (607 : ℤ) ^ 3 ∣
      a * vandiverBernoulliNumerator 607 k := by
  apply
    Fermat.Irregular.VandiverDerivativeValuationPrime.cube_dvd_exponent_mul_bernoulliNumerator_of_derivative
      (p := 607) (r := 303) (t := 813)
      (by norm_num) teichmullerRoot607_isPrimitive
      149281434 (by norm_num) k a
  simpa [diagonalDerivativeFactor607, derivativeBernoulliIndex607,
    diagonalDerivativeFactor, derivativeBernoulliIndex] using hderivative

end Fermat.SixHundredSeven.VandiverDerivativeValuation
