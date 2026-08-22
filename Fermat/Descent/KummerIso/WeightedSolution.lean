import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Divisibility.Basic

/-!
# The weighted solution produced by Kummer's induction

The regular-style cyclotomic induction first produces an equation with three unit
coefficients.  Its next unit-theoretic step concerns the particular quotient
`ε₁ / ε₂`, rather than an arbitrary semiprimary unit.  This file gives that
intermediate object a small, reusable interface.

The structure records algebraic data only.  In particular, it contains
neither a principalization hypothesis nor a conclusion that `unitRatio` is a
`p`-th power.  It also makes no identification with the independently
constructed weighted ratio in
`VandiverHistoricalPrime.WeightedReductionData`; such an identification
would require a separate bridge theorem.
-/

namespace Fermat.KummerIso

/-- A weighted Fermat equation at descent depth `m`, together with the
nondivisibility facts needed by the next induction step. -/
structure WeightedSolution (R : Type*) [CommRing R]
    (p m : ℕ) (π : R) where
  x : R
  y : R
  z : R
  ε₁ : Rˣ
  ε₂ : Rˣ
  ε₃ : Rˣ
  not_pi_dvd_x : ¬ π ∣ x
  not_pi_dvd_y : ¬ π ∣ y
  not_pi_dvd_z : ¬ π ∣ z
  equation :
    (ε₁ : R) * x ^ p + (ε₂ : R) * y ^ p =
      (ε₃ : R) * (π ^ m * z) ^ p

namespace WeightedSolution

variable {R : Type*} [CommRing R] {p m : ℕ} {π : R}

/-- The exact unit quotient whose `p`-th-power status removes the weights
from Kummer's next descent equation. -/
def unitRatio (w : WeightedSolution R p m π) : Rˣ :=
  w.ε₁ / w.ε₂

@[simp]
theorem unitRatio_eq (w : WeightedSolution R p m π) :
    w.unitRatio = w.ε₁ / w.ε₂ :=
  rfl

end WeightedSolution

end Fermat.KummerIso
