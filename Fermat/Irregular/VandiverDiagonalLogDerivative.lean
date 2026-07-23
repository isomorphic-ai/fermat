import Fermat.Irregular.VandiverPowerSeriesLog

/-!
# Vandiver's diagonal cyclotomic-unit logarithms

This file formalizes the source-faithful product which Vandiver denotes by
`E_i(w)` on p. 617.  If

`ε(w) = w^e (w^r - 1) / (w - 1)`,

then substitution `w = exp X` turns `ε(w^(r^j))` into a normalized
geometric exponential.  Vandiver takes `j = 0, ..., (p - 3) / 2` and the
weights `r^(-2ij)`.  To stay inside integral polynomials he raises the
product to `ρ = r^(p^2)`, producing the positive weights
`r^(p^2 - 2ij)` used below.

The theorems here are exact identities over `ℚ`.  Reduction modulo `p^2`
and the resulting diagonal character sum are kept in the finite-arithmetic
specialization.
-/

namespace Fermat.Irregular.VandiverDiagonalLogDerivative

open PowerSeries
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog

noncomputable section

/-- `ε(exp (sX))`, where `ε(w) = w^e (w^r - 1) / (w - 1)`.
The quotient is represented by its geometric sum, so this definition is
purely formal and has no singular denominator. -/
def normalizedGeomExp (r e s : ℕ) : PowerSeries ℚ :=
  PowerSeries.exp ℚ ^ (e * s) *
    PowerSeries.rescale (s : ℚ) (geomExp r)

@[simp]
theorem constantCoeff_normalizedGeomExp (r e s : ℕ) :
    PowerSeries.constantCoeff (normalizedGeomExp r e s) = (r : ℚ) := by
  simp [normalizedGeomExp]

/-- Exact logarithmic derivative of a normalized cyclotomic geometric
factor.  The normalization monomial contributes only the constant
`e*s`; every positive derivative therefore comes from Vandiver's
Bernoulli series. -/
theorem logarithmicDerivative_normalizedGeomExp
    (r e s : ℕ) (hr : 0 < r) :
    logarithmicDerivative (normalizedGeomExp r e s) =
      PowerSeries.C ((e * s : ℕ) : ℚ) +
        PowerSeries.C (s : ℚ) *
          PowerSeries.rescale (s : ℚ)
            (vandiverLogDerivative (r : ℚ)) := by
  have hgeom : PowerSeries.constantCoeff (geomExp r) ≠ 0 := by
    rw [constantCoeff_geomExp]
    exact_mod_cast Nat.ne_of_gt hr
  have hexp : PowerSeries.constantCoeff
      (PowerSeries.exp ℚ ^ (e * s)) ≠ 0 := by simp
  have hscaled : PowerSeries.constantCoeff
      (PowerSeries.rescale (s : ℚ) (geomExp r)) ≠ 0 := by
    simpa using hgeom
  calc
    logarithmicDerivative (normalizedGeomExp r e s) =
        logarithmicDerivative (PowerSeries.exp ℚ ^ (e * s)) +
          logarithmicDerivative
            (PowerSeries.rescale (s : ℚ) (geomExp r)) := by
      rw [normalizedGeomExp,
        logarithmicDerivative_mul _ _ hexp hscaled]
    _ = PowerSeries.C ((e * s : ℕ) : ℚ) +
        PowerSeries.C (s : ℚ) *
          PowerSeries.rescale (s : ℚ)
            (vandiverLogDerivative (r : ℚ)) := by
      rw [logarithmicDerivative_pow _ _ (by simp),
        logarithmicDerivative_exp,
        logarithmicDerivative_rescale _ _ hgeom,
        logarithmicDerivative_geomExp r hr]
      simp

/-- Every positive derivative of a normalized factor is the rescaled
derivative of the one basic Vandiver series. -/
theorem formalDerivativeAtZero_logarithmicDerivative_normalizedGeomExp
    (r e s n : ℕ) (hr : 0 < r) (hn : 0 < n) :
    formalDerivativeAtZero n
        (logarithmicDerivative (normalizedGeomExp r e s)) =
      (s : ℚ) ^ (n + 1) *
        formalDerivativeAtZero n
          (vandiverLogDerivative (r : ℚ)) := by
  rw [logarithmicDerivative_normalizedGeomExp r e s hr,
    formalDerivativeAtZero_add, formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_rescale]
  have hconstant :
      formalDerivativeAtZero n
          (PowerSeries.C ((e * s : ℕ) : ℚ)) = 0 := by
    rw [formalDerivativeAtZero,
      PowerSeries.coeff_C_of_ne_zero (Nat.ne_of_gt hn)]
    ring
  rw [hconstant, zero_add, pow_succ]
  ring

/-- Vandiver's integral replacement for the negative exponent
`r^(-2ij)` after multiplying all exponents by `ρ = r^(p^2)`. -/
def integralDiagonalWeight (p r i j : ℕ) : ℕ :=
  r ^ (p ^ 2 - 2 * i * j)

/-- The `j`th factor of the integral polynomial `E_i(w)^ρ`. -/
def integralDiagonalFactor (p r e i j : ℕ) : PowerSeries ℚ :=
  normalizedGeomExp r e (r ^ j) ^ integralDiagonalWeight p r i j

/-- The integral polynomial version of Vandiver's diagonal unit.  The
range has `(p - 1) / 2` terms, namely source indices
`j = 0, ..., (p - 3) / 2`. -/
def integralDiagonalExp (p r e i : ℕ) : PowerSeries ℚ :=
  ∏ j ∈ Finset.range ((p - 1) / 2),
    integralDiagonalFactor p r e i j

@[simp]
theorem constantCoeff_integralDiagonalFactor
    (p r e i j : ℕ) :
    PowerSeries.constantCoeff (integralDiagonalFactor p r e i j) =
      (r : ℚ) ^ integralDiagonalWeight p r i j := by
  simp [integralDiagonalFactor]

/-- The logarithmic derivative of Vandiver's integral diagonal product
is the weighted sum of the basic normalized factors. -/
theorem logarithmicDerivative_integralDiagonalExp
    (p r e i : ℕ) (hr : 0 < r) :
    logarithmicDerivative (integralDiagonalExp p r e i) =
      ∑ j ∈ Finset.range ((p - 1) / 2),
        PowerSeries.C (integralDiagonalWeight p r i j : ℚ) *
          logarithmicDerivative (normalizedGeomExp r e (r ^ j)) := by
  rw [integralDiagonalExp, logarithmicDerivative_prod]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integralDiagonalFactor,
      logarithmicDerivative_pow _ _ (by
        rw [constantCoeff_normalizedGeomExp]
        exact_mod_cast Nat.ne_of_gt hr)]
  · intro j hj
    rw [constantCoeff_integralDiagonalFactor]
    apply pow_ne_zero
    exact_mod_cast Nat.ne_of_gt hr

/-- Exact high-derivative character sum for Vandiver's integral diagonal
product.  The finite coefficient sum is the object which becomes diagonal
modulo `p^2` after choosing a Teichmüller primitive root. -/
theorem formalDerivativeAtZero_logarithmicDerivative_integralDiagonalExp
    (p r e i n : ℕ) (hr : 0 < r) (hn : 0 < n) :
    formalDerivativeAtZero n
        (logarithmicDerivative (integralDiagonalExp p r e i)) =
      (∑ j ∈ Finset.range ((p - 1) / 2),
          (integralDiagonalWeight p r i j : ℚ) *
            (r ^ j : ℚ) ^ (n + 1)) *
        formalDerivativeAtZero n
          (vandiverLogDerivative (r : ℚ)) := by
  rw [logarithmicDerivative_integralDiagonalExp p r e i hr,
    formalDerivativeAtZero_sum]
  simp_rw [formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_logarithmicDerivative_normalizedGeomExp
      r e _ n hr hn]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.cast_pow]
  ring

end

end Fermat.Irregular.VandiverDiagonalLogDerivative
