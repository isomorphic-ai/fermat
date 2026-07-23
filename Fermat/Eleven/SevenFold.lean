import Fermat.Classical
import Fermat.Eleven.Cyclotomic
import Fermat.Five.Dirichlet
import Fermat.Regular.KummerCriterion

/-!
# The decompressed seven-fold package at exponent eleven

This file retains the structural route from the uploaded exponent-`11`
package alongside the shorter class-number-one proof.  In particular, its
Bernoulli layer is proved directly by four finite Faulhaber power sums; it
does not use Kummer's congruence.

The class-number-one certificate already closes FLT at stage 6.  The
Faulhaber branch now supplies a second, logically independent endpoint:
the formal Kummer criterion turns its four Bernoulli numerator certificates
into `IsRegularPrime 11`, and the checked `flt_regular` descent closes FLT.
-/

namespace Fermat.Eleven.SevenFold

open Fermat.Regular.Faulhaber
open Finset

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-! ## 1. Neighbor substrate -/

/-- The left neighbor is already supplied by the historical exponent-five
descent. -/
theorem holdsAt_ten : Fermat.HoldsAt 10 :=
  Fermat.HoldsAt.mono_of_dvd Fermat.Five.Dirichlet.holdsAt_five_dirichlet
    (by norm_num)

/-- The right neighbor is supplied by the exponent-three descent. -/
theorem holdsAt_twelve : Fermat.HoldsAt 12 :=
  Fermat.HoldsAt.mono_of_dvd Fermat.holdsAt_three (by norm_num)

/-! ## 2--5. Circle, quadratic crease, Gauss object, and norm identity -/

/-- `(X^11 + Y^11) / (X + Y)` in homogeneous form. -/
def phi22 (x y : ℤ) : ℤ :=
  ∑ j ∈ range 11, (-1 : ℤ) ^ j * x ^ (10 - j) * y ^ j

def quadraticA (x y : ℤ) : ℤ :=
  (x + y) *
    (2*x^4 - 3*x^3*y + x^2*y^2 - 3*x*y^3 + 2*y^4)

def quadraticB (x y : ℤ) : ℤ :=
  x * y * (x - y) * (x^2 + x*y + y^2)

/-- The exact quadratic-period norm from `ℚ(√-11)`. -/
theorem quadratic_fold (x y : ℤ) :
    quadraticA x y ^ 2 + 11 * quadraticB x y ^ 2 =
      4 * phi22 x y := by
  norm_num [quadraticA, quadraticB, phi22, Finset.sum_range_succ]
  ring

def C (x y : ℤ) : ℤ := x^2 - x*y + y^2

def D (x y : ℤ) : ℤ := x*y*(x-y)

def psi11 (x y : ℤ) : ℤ :=
  ∑ j ∈ range 11, x ^ (10 - j) * y ^ j

/-- The package's secondary composition through the exponent-seven forms
`C` and `D`. -/
theorem secondary_composition (x y : ℤ) :
    psi11 x y =
      (x - y)^10 + 11*x*y*C x y*(C x y ^ 3 + D x y ^ 2) := by
  norm_num [psi11, C, D, Finset.sum_range_succ]
  ring

/-! ## 6. Global branch selection -/

/-- The exact norm-23/Minkowski certificate supplies the global branch
selection and, in fact, is already sufficient for the descent. -/
theorem classNumber_branch : IsRegularPrime 11 :=
  Fermat.Eleven.Cyclotomic.isRegularPrime_eleven

/-! ## 7. Decompressed Bernoulli/Faulhaber stratum -/

/-- Each low even power sum is nonzero modulo `11^2`. -/
theorem powerSum_not_dvd_sq {k : ℕ} (hk : k ∈ regularIndices 11) :
    ¬(11 : ℤ) ^ 2 ∣ powerSum 11 k := by
  simp only [regularIndices, Finset.mem_filter, Finset.mem_Icc] at hk
  rcases hk with ⟨⟨hk2, hk8⟩, heven⟩
  interval_cases k <;> norm_num at heven
  all_goals
    norm_num [powerSum, Finset.sum_Ico_eq_sub, Finset.sum_range_succ]

/-- All four low Bernoulli numerators for `11` are certified directly from
Faulhaber's formula. -/
theorem bernoulliNumeratorRegular_eleven :
    BernoulliNumeratorRegular 11 :=
  bernoulliNumeratorRegular_of_powerSums (by norm_num)
    (fun _ hk ↦ powerSum_not_dvd_sq hk)

theorem isRegularPrime_eleven_faulhaber :
    IsRegularPrime 11 :=
  isRegularPrime_of_bernoulliNumeratorRegular (by norm_num)
    bernoulliNumeratorRegular_eleven

/-! ## 8. Checked descent engine -/

/-- The complete alternative endpoint whose regularity premise is supplied
by the direct four-index Faulhaber computation. -/
theorem holdsAt_eleven_faulhaber : Fermat.HoldsAt 11 :=
  holdsAt_of_bernoulliNumeratorRegular (by norm_num)
    bernoulliNumeratorRegular_eleven

/-- Backwards-compatible name for the decompressed seven-fold endpoint. -/
theorem holdsAt_eleven_sevenFold : Fermat.HoldsAt 11 :=
  holdsAt_eleven_faulhaber

/-- A compact public package showing that both the decompressed Bernoulli
layer and the final exponent theorem are joined by Kummer's criterion. -/
theorem faulhaber_and_flt_eleven :
    BernoulliNumeratorRegular 11 ∧ Fermat.HoldsAt 11 :=
  let hregular := bernoulliNumeratorRegular_eleven
  ⟨hregular,
    holdsAt_of_bernoulliNumeratorRegular (by norm_num) hregular⟩

end Fermat.Eleven.SevenFold
