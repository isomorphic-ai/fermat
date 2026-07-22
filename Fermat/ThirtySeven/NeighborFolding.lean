import Fermat.Basic

/-!
# The exponent-thirty-seven neighbor-folding certificate

This file formalizes the exact polynomial identities in the uploaded
`flt_37_neighbor_folding` package.  They explain how the order-`36`
cyclotomic orbit simultaneously exposes the earlier exponent-`13`,
exponent-`11`, and exponent-`7` certificates.

These identities are certificate-generating structure; the irregular-prime
descent needed to conclude FLT for exponent `37` is kept separate.
-/

namespace Fermat.ThirtySeven.NeighborFolding

open Finset

/-- The homogeneous cyclotomic quotient
`(X^37 + Y^37) / (X + Y) = Phi_74(X,Y)`. -/
def phi74 (x y : ℤ) : ℤ :=
  ∑ j ∈ range 37, (-1 : ℤ) ^ j * x ^ (36 - j) * y ^ j

/-! ## The direct quadratic-residue fold -/

def quadraticP0 (x y : ℤ) : ℤ :=
  x^18 + 5*x^16*y^2 + 3*x^15*y^3 + 8*x^14*y^4 + 4*x^13*y^5 +
  9*x^12*y^6 + 5*x^11*y^7 + 6*x^10*y^8 + 3*x^9*y^9 +
  6*x^8*y^10 + 5*x^7*y^11 + 9*x^6*y^12 + 4*x^5*y^13 +
  8*x^4*y^14 + 3*x^3*y^15 + 5*x^2*y^16 + y^18

def quadraticP1 (x y : ℤ) : ℤ :=
  x^17*y + 2*x^15*y^3 + x^14*y^4 + 3*x^13*y^5 + x^12*y^6 +
  2*x^11*y^7 + x^10*y^8 + 2*x^9*y^9 + x^8*y^10 +
  2*x^7*y^11 + x^6*y^12 + 3*x^5*y^13 + x^4*y^14 +
  2*x^3*y^15 + x*y^17

def A37 (x y : ℤ) : ℤ := 2 * quadraticP0 x y - quadraticP1 x y

def B37 (x y : ℤ) : ℤ := quadraticP1 x y

/-- The exact `36 → 18` quadratic fold from the package. -/
theorem quadratic_fold (x y : ℤ) :
    A37 x y ^ 2 - 37 * B37 x y ^ 2 = 4 * phi74 x y := by
  norm_num [A37, B37, quadraticP0, quadraticP1, phi74, Finset.sum_range_succ]
  ring

/-! ## The literal exponent-thirteen certificate inside `B37` -/

def B13 (x y : ℤ) : ℤ :=
  x * y * (x^2 - x*y + y^2) * (x^2 + x*y + y^2)

def Q12 (x y : ℤ) : ℤ :=
  x^12 + x^10*y^2 + x^9*y^3 + x^8*y^4 + x^4*y^8 +
  x^3*y^9 + x^2*y^10 + y^12

/-- The package's literal reused exponent-`13` factor. -/
theorem B37_eq_B13_mul_Q12 (x y : ℤ) :
    B37 x y = B13 x y * Q12 x y := by
  simp only [B37, quadraticP1, B13, Q12]
  ring

def A13 (x y : ℤ) : ℤ :=
  2*x^6 - x^5*y + 4*x^4*y^2 + x^3*y^3 +
  4*x^2*y^4 - x*y^5 + 2*y^6

def phi26 (x y : ℤ) : ℤ :=
  ∑ j ∈ range 13, (-1 : ℤ) ^ j * x ^ (12 - j) * y ^ j

/-- The embedded exponent-`13` quadratic identity. -/
theorem thirteen_fold (x y : ℤ) :
    A13 x y ^ 2 - 13 * B13 x y ^ 2 = 4 * phi26 x y := by
  norm_num [A13, B13, phi26, Finset.sum_range_succ]
  ring

/-! ## The index-three (`3 × 12`) Gaussian-period fold -/

def cubicP0 (x y : ℤ) : ℤ :=
  x^12 + 4*x^10*y^2 + 6*x^9*y^3 + 9*x^8*y^4 + 10*x^7*y^5 +
  7*x^6*y^6 + 10*x^5*y^7 + 9*x^4*y^8 + 6*x^3*y^9 +
  4*x^2*y^10 + y^12

def cubicP1 (x y : ℤ) : ℤ :=
  x^11*y - x^10*y^2 - x^9*y^3 - 3*x^8*y^4 - 3*x^7*y^5 -
  x^6*y^6 - 3*x^5*y^7 - 3*x^4*y^8 - x^3*y^9 -
  x^2*y^10 + x*y^11

def cubicP2 (x y : ℤ) : ℤ :=
  -x^9*y^3 - x^8*y^4 - x^7*y^5 - x^6*y^6 -
  x^5*y^7 - x^4*y^8 - x^3*y^9

/-- The norm form for `T^3 + T^2 - 12T + 11`. -/
def cubicNorm (a b c : ℤ) : ℤ :=
  a^3 - a^2*b + 25*a^2*c - 12*a*b^2 + 45*a*b*c +
  122*a*c^2 - 11*b^3 + 11*b^2*c + 132*b*c^2 + 121*c^3

/-- Determinant of multiplication by `a + b*T + c*T²` in the basis
`1,T,T²`, after reducing by `T³ + T² - 12T + 11`. -/
def cubicMultiplicationDet (a b c : ℤ) : ℤ :=
  a * ((a + 12*c) * (a - b + 13*c) - (12*b - 23*c) * (b - c)) -
  (-11*c) * (b * (a - b + 13*c) - (12*b - 23*c) * c) +
  (-11*b + 11*c) * (b * (b - c) - (a + 12*c) * c)

theorem cubicMultiplicationDet_eq_cubicNorm (a b c : ℤ) :
    cubicMultiplicationDet a b c = cubicNorm a b c := by
  simp only [cubicMultiplicationDet, cubicNorm]
  ring

/-- The cubic Gaussian-period polynomial has discriminant `37²`. -/
theorem period_polynomial_discriminant :
    (1 : ℤ)^2 * (-12)^2 - 4*(-12)^3 - 4*1^3*11 - 27*11^2 +
      18*1*(-12)*11 = 37^2 := by
  norm_num

/-- The exact `3 × 12` norm fold from the package. -/
theorem cubic_fold (x y : ℤ) :
    cubicNorm (cubicP0 x y) (cubicP1 x y) (cubicP2 x y) = phi74 x y := by
  norm_num [cubicNorm, cubicP0, cubicP1, cubicP2, phi74, Finset.sum_range_succ]
  ring

def psi7 (x y : ℤ) : ℤ :=
  x^6 + x^5*y + x^4*y^2 + x^3*y^3 + x^2*y^4 + x*y^5 + y^6

def phi22 (x y : ℤ) : ℤ :=
  ∑ j ∈ range 11, (-1 : ℤ) ^ j * x ^ (10 - j) * y ^ j

def R4 (x y : ℤ) : ℤ :=
  x^4 - 2*x^3*y + x^2*y^2 - 2*x*y^3 + y^4

def cubicP1Quotient (x y : ℤ) : ℤ :=
  x^10 - x^9*y - x^8*y^2 - 3*x^7*y^3 - 3*x^6*y^4 -
  x^5*y^5 - 3*x^4*y^6 - 3*x^3*y^7 - x^2*y^8 - x*y^9 + y^10

theorem cubicP1_eq_mul_quotient (x y : ℤ) :
    cubicP1 x y = x * y * cubicP1Quotient x y := by
  simp only [cubicP1, cubicP1Quotient]
  ring

/-- The exponent-`7` factor carried by the third cubic coefficient. -/
theorem cubicP2_contains_seven (x y : ℤ) :
    cubicP2 x y = -(x^3 * y^3 * psi7 x y) := by
  simp only [cubicP2, psi7]
  ring

/-- The exponent-`11` and exponent-`7` factors carried together by the
second cubic coefficient. -/
theorem cubicP1_contains_eleven_and_seven (x y : ℤ) :
    cubicP1Quotient x y + phi22 x y = 2 * R4 x y * psi7 x y := by
  norm_num [cubicP1Quotient, phi22, R4, psi7, Finset.sum_range_succ]
  ring

/-- Specializing the cubic period to `T = 2` exposes a cyclotomic-unit
factorization; the period polynomial takes the unit value `-1` there. -/
theorem cubic_unit_specialization (x y : ℤ) :
    cubicP0 x y + 2*cubicP1 x y + 4*cubicP2 x y =
      (x^2 + x*y + y^2)^2 *
        (x^8 - x^6*y^2 + x^4*y^4 - x^2*y^6 + y^8) := by
  simp only [cubicP0, cubicP1, cubicP2]
  ring

theorem period_polynomial_at_two : (2 : ℤ)^3 + 2^2 - 12*2 + 11 = -1 := by
  norm_num

end Fermat.ThirtySeven.NeighborFolding
