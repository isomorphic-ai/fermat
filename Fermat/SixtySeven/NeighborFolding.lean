import Fermat.Eleven.SevenFold
import Fermat.ThirtySeven.NeighborFolding

/-!
# Neighbor folding at exponent 67

This file kernel-checks the exact rational quadratic fold and scalar
`B`-tower from the uploaded exponent-`67` package.  It also records the two
genuine exits of the neighboring composite exponent `66`, through exponents
`3` and `11`.

The independent exponent-13 channel of the package is deliberately linked to
the already checked coordinate from `Fermat.ThirtySeven.NeighborFolding`;
this makes reuse, rather than a merely visually similar polynomial, part of
the theorem statement.
-/

namespace Fermat.SixtySeven.NeighborFolding

open Finset

/-! ## The neighboring exponent -/

theorem holdsAt_sixtySix_via_three : Fermat.HoldsAt 66 :=
  Fermat.HoldsAt.mono_of_dvd Fermat.holdsAt_three (by norm_num)

theorem holdsAt_sixtySix_via_eleven : Fermat.HoldsAt 66 :=
  Fermat.HoldsAt.mono_of_dvd
    Fermat.Eleven.SevenFold.holdsAt_eleven_sevenFold (by norm_num)

/-! ## The direct quadratic-residue fold -/

/-- The homogeneous cyclotomic quotient
`(X^67 + Y^67) / (X + Y) = Φ₁₃₄(X,Y)`. -/
def phi134 (x y : ℤ) : ℤ :=
  ∑ j ∈ range 67, (-1 : ℤ) ^ j * x ^ (66 - j) * y ^ j

def A67 (x y : ℤ) : ℤ :=
  2*x^33 - x^32*y - 16*x^31*y^2 - 9*x^30*y^3 + 33*x^29*y^4 +
  44*x^28*y^5 - 18*x^27*y^6 - 79*x^26*y^7 - 39*x^25*y^8 +
  48*x^24*y^9 + 75*x^23*y^10 + 35*x^22*y^11 - 14*x^21*y^12 -
  69*x^20*y^13 - 89*x^19*y^14 - 10*x^18*y^15 + 106*x^17*y^16 +
  106*x^16*y^17 - 10*x^15*y^18 - 89*x^14*y^19 - 69*x^13*y^20 -
  14*x^12*y^21 + 35*x^11*y^22 + 75*x^10*y^23 + 48*x^9*y^24 -
  39*x^8*y^25 - 79*x^7*y^26 - 18*x^6*y^27 + 44*x^5*y^28 +
  33*x^4*y^29 - 9*x^3*y^30 - 16*x^2*y^31 - x*y^32 + 2*y^33

def B67 (x y : ℤ) : ℤ :=
  x^32*y - 3*x^30*y^3 - 3*x^29*y^4 + 4*x^28*y^5 + 8*x^27*y^6 +
  x^26*y^7 - 9*x^25*y^8 - 8*x^24*y^9 + x^23*y^10 +
  7*x^22*y^11 + 8*x^21*y^12 + 5*x^20*y^13 - 5*x^19*y^14 -
  14*x^18*y^15 - 8*x^17*y^16 + 8*x^16*y^17 + 14*x^15*y^18 +
  5*x^14*y^19 - 5*x^13*y^20 - 8*x^12*y^21 - 7*x^11*y^22 -
  x^10*y^23 + 8*x^9*y^24 + 9*x^8*y^25 - x^7*y^26 -
  8*x^6*y^27 - 4*x^5*y^28 + 3*x^4*y^29 + 3*x^3*y^30 - x*y^32

/-- The exact `66 → 33` quadratic-period norm identity. -/
theorem quadratic_fold (x y : ℤ) :
    A67 x y ^ 2 + 67 * B67 x y ^ 2 = 4 * phi134 x y := by
  norm_num [A67, B67, phi134, Finset.sum_range_succ]
  ring

/-! ## The exact scalar B-tower -/

def B7 (x y : ℤ) : ℤ := x * y * (x - y)

def phi3 (x y : ℤ) : ℤ := x^2 + x*y + y^2

def B11 (x y : ℤ) : ℤ :=
  x*y*(x-y)*(x^2+x*y+y^2)

def phi12 (x y : ℤ) : ℤ := x^4 - x^2*y^2 + y^4

def B19 (x y : ℤ) : ℤ :=
  x*y*(x-y)*(x^2+x*y+y^2)*(x^4-x^2*y^2+y^4)

def Q24 (x y : ℤ) : ℤ :=
  x^24 - 2*x^22*y^2 - 2*x^21*y^3 + x^20*y^4 + 3*x^19*y^5 +
  2*x^18*y^6 - 2*x^16*y^8 - 3*x^15*y^9 - 2*x^14*y^10 +
  2*x^13*y^11 + 5*x^12*y^12 + 2*x^11*y^13 - 2*x^10*y^14 -
  3*x^9*y^15 - 2*x^8*y^16 + 2*x^6*y^18 + 3*x^5*y^19 +
  x^4*y^20 - 2*x^3*y^21 - 2*x^2*y^22 + y^24

theorem B11_eq_B7_mul_phi3 (x y : ℤ) :
    B11 x y = B7 x y * phi3 x y := by
  simp only [B11, B7, phi3]

theorem B19_eq_B11_mul_phi12 (x y : ℤ) :
    B19 x y = B11 x y * phi12 x y := by
  simp only [B19, B11, phi12]

/-- The package's sharp factorization of the square-root coordinate. -/
theorem B67_eq_B19_mul_Q24 (x y : ℤ) :
    B67 x y = B19 x y * Q24 x y := by
  simp only [B67, B19, Q24]
  ring

/-- Consequently all three historical lower coordinates divide the
exponent-67 square-root coordinate. -/
theorem B7_dvd_B11_dvd_B19_dvd_B67 (x y : ℤ) :
    B7 x y ∣ B11 x y ∧ B11 x y ∣ B19 x y ∧ B19 x y ∣ B67 x y := by
  refine ⟨⟨phi3 x y, B11_eq_B7_mul_phi3 x y⟩,
    ⟨⟨phi12 x y, B19_eq_B11_mul_phi12 x y⟩, ?_⟩⟩
  exact ⟨Q24 x y, B67_eq_B19_mul_Q24 x y⟩

/-- The independent exponent-`13` coordinate used by the package's
`3 × 22` subgroup fold is not re-proved here: it is the already checked
coordinate from the exponent-37 development. -/
abbrev embeddedB13 : ℤ → ℤ → ℤ :=
  Fermat.ThirtySeven.NeighborFolding.B13

theorem reused_thirteen_fold (x y : ℤ) :
    Fermat.ThirtySeven.NeighborFolding.A13 x y ^ 2 -
        13 * embeddedB13 x y ^ 2 =
      4 * Fermat.ThirtySeven.NeighborFolding.phi26 x y :=
  Fermat.ThirtySeven.NeighborFolding.thirteen_fold x y

end Fermat.SixtySeven.NeighborFolding
