import Fermat.Classical
import Fermat.Fourteen.DescentConstruction
import Fermat.Regular.Faulhaber
import Fermat.Thirteen.Cyclotomic

/-!
# The decompressed seven-fold package at exponent thirteen

This file retains the structural route from the uploaded exponent-`13`
package alongside the shorter class-number-one proof.  Its Bernoulli layer
is proved directly by five finite Faulhaber power sums, independently of
Kummer's congruence.

The class-number-one certificate already closes FLT at stage 6.  Thus the
Faulhaber branch records the decompressed coefficient structure but is not a
premise of the final `flt_regular` call.  A proof that this numerical branch
alone implies `IsRegularPrime 13` would be Kummer's deeper regular-prime
criterion, presently absent from Mathlib.
-/

namespace Fermat.Thirteen.SevenFold

open Fermat.Regular.Faulhaber
open Finset

local instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-! ## 1. Neighbor substrate -/

/-- The left neighbor is supplied by the exponent-three/four descent
network. -/
theorem holdsAt_twelve : Fermat.HoldsAt 12 :=
  Fermat.HoldsAt.mono_of_dvd Fermat.holdsAt_three (by norm_num)

/-- The right neighbor is the independently formalized old Dirichlet
exponent-fourteen descent. -/
theorem holdsAt_fourteen : Fermat.HoldsAt 14 :=
  Fermat.Fourteen.Dirichlet.holdsAt_fourteen_dirichlet

/-! ## 2--5. Circle, quadratic crease, Gauss object, and norm identity -/

/-- `(X^13 + Y^13) / (X + Y)` in homogeneous form. -/
def phi26 (x y : ℤ) : ℤ :=
  ∑ j ∈ range 13, (-1 : ℤ) ^ j * x ^ (12 - j) * y ^ j

def quadraticA (x y : ℤ) : ℤ :=
  2*x^6 - x^5*y + 4*x^4*y^2 + x^3*y^3 +
    4*x^2*y^4 - x*y^5 + 2*y^6

def quadraticB (x y : ℤ) : ℤ :=
  x*y*(x^2 - x*y + y^2)*(x^2 + x*y + y^2)

/-- The exact quadratic-period norm from `ℚ(√13)`. -/
theorem quadratic_fold (x y : ℤ) :
    quadraticA x y ^ 2 - 13 * quadraticB x y ^ 2 =
      4 * phi26 x y := by
  norm_num [quadraticA, quadraticB, phi26, Finset.sum_range_succ]
  ring

def C (x y : ℤ) : ℤ := x^2 - x*y + y^2

def D (x y : ℤ) : ℤ := x*y*(x-y)

def psi13 (x y : ℤ) : ℤ :=
  ∑ j ∈ range 13, x ^ (12 - j) * y ^ j

/-- The package's secondary composition through the same exponent-seven
forms `C` and `D`, with one additional composition layer. -/
theorem secondary_composition (x y : ℤ) :
    psi13 x y =
      (x - y)^12 + 13*x*y*C x y^2*(C x y ^ 3 + 2*D x y ^ 2) := by
  norm_num [psi13, C, D, Finset.sum_range_succ]
  ring

/-! ## 6. Global branch selection -/

/-- The five norm certificates and the exact Minkowski bound supply the
global branch selection and are already sufficient for the descent. -/
theorem classNumber_branch : IsRegularPrime 13 :=
  Fermat.Thirteen.Cyclotomic.isRegularPrime_thirteen

/-! ## 7. Decompressed Bernoulli/Faulhaber stratum -/

/-- Each low even power sum is nonzero modulo `13^2`. -/
theorem powerSum_not_dvd_sq {k : ℕ} (hk : k ∈ regularIndices 13) :
    ¬(13 : ℤ) ^ 2 ∣ powerSum 13 k := by
  simp only [regularIndices, Finset.mem_filter, Finset.mem_Icc] at hk
  rcases hk with ⟨⟨hk2, hk10⟩, heven⟩
  interval_cases k <;> norm_num at heven
  all_goals
    norm_num [powerSum, Finset.sum_Ico_eq_sub, Finset.sum_range_succ]

/-- All five low Bernoulli numerators for `13` are certified directly from
Faulhaber's formula. -/
theorem bernoulliNumeratorRegular_thirteen :
    BernoulliNumeratorRegular 13 :=
  bernoulliNumeratorRegular_of_powerSums (by norm_num)
    (fun _ hk ↦ powerSum_not_dvd_sq hk)

/-! ## 8. Checked descent engine -/

/-- The complete endpoint retained beside the decompressed certificates.
The class-number branch is the first sufficient branch in this instance. -/
theorem holdsAt_thirteen_sevenFold : Fermat.HoldsAt 13 :=
  Fermat.Thirteen.Cyclotomic.holdsAt_thirteen_cyclotomic

/-- A compact public package showing that both the decompressed Bernoulli
layer and the final exponent theorem have been checked. -/
theorem faulhaber_and_flt_thirteen :
    BernoulliNumeratorRegular 13 ∧ Fermat.HoldsAt 13 :=
  ⟨bernoulliNumeratorRegular_thirteen, holdsAt_thirteen_sevenFold⟩

end Fermat.Thirteen.SevenFold
