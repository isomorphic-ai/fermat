/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The golden-ring conservation spine at exponent five

This file isolates the algebraic ledger used by the conservation proof of
FLT(5).  It deliberately imports no earlier repository module under
`Fermat.Five`: the golden ring, its gauge-invariant charge, the quintic
ledger, and the ramified drain quantum are rebuilt at the minimal statement
boundary.

Write `φ` for a root of `φ² = φ + 1`.  The quadratic algebra
`QuadraticAlgebra ℤ 1 1` is the integral golden ring `ℤ[φ]`, and the norm of
`x + yφ` is `x² + xy - y²`.
-/
import Fermat.Statement
import Fermat.Conservation.Floor
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Ring

namespace Fermat.Five.Conservation

/-- The integral golden ring `ℤ[φ]`, presented by `φ² = φ + 1`. -/
abbrev GoldenInt := QuadraticAlgebra ℤ 1 1

/-- The signed golden-ring norm `N(x + yφ) = x² + xy - y²`. -/
abbrev goldenNorm : GoldenInt →* ℤ := QuadraticAlgebra.norm

/-- The nonnegative ledger charge: the absolute golden-ring norm. -/
def goldenCharge (z : GoldenInt) : ℕ :=
  (goldenNorm z).natAbs

/-- Signed norm is multiplicatively conserved. -/
theorem goldenNorm_mul (z w : GoldenInt) :
    goldenNorm (z * w) = goldenNorm z * goldenNorm w :=
  map_mul goldenNorm z w

/-- Absolute norm charge is multiplicatively conserved. -/
theorem goldenCharge_mul (z w : GoldenInt) :
    goldenCharge (z * w) = goldenCharge z * goldenCharge w := by
  simp only [goldenCharge, goldenNorm_mul, Int.natAbs_mul]

/-- Every golden-ring unit has signed norm `1` or `-1`. -/
theorem goldenNorm_unit_eq_one_or_neg_one (u : GoldenIntˣ) :
    goldenNorm (u : GoldenInt) = 1 ∨
      goldenNorm (u : GoldenInt) = -1 := by
  apply Int.isUnit_eq_one_or
  exact QuadraticAlgebra.isUnit_iff_norm_isUnit.mp u.isUnit

/-- A golden-ring unit carries exactly one unit of absolute norm charge. -/
theorem goldenCharge_unit (u : GoldenIntˣ) :
    goldenCharge (u : GoldenInt) = 1 := by
  apply Int.natAbs_of_isUnit
  exact QuadraticAlgebra.isUnit_iff_norm_isUnit.mp u.isUnit

/-- **Gauge invariance at exponent five.** Multiplication by any unit of the
infinite golden-ring unit group leaves the observable charge unchanged. -/
theorem charge_gauge_invariant (u : GoldenIntˣ) (z : GoldenInt) :
    goldenCharge ((u : GoldenInt) * z) = goldenCharge z := by
  rw [goldenCharge_mul, goldenCharge_unit, one_mul]

/-- The quartic cofactor in the factorization of a sum of fifth powers. -/
def quinticCofactor (a b : ℤ) : ℤ :=
  a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4

/-- The golden-ring element whose norm is the quintic cofactor. -/
def quinticCofactorElement (a b : ℤ) : GoldenInt :=
  ⟨a ^ 2 + b ^ 2, -(a * b)⟩

/-- The quintic cofactor is a golden-ring norm form. -/
theorem quinticCofactor_eq_goldenNorm (a b : ℤ) :
    quinticCofactor a b =
      goldenNorm (quinticCofactorElement a b) := by
  simp only [quinticCofactor, goldenNorm, quinticCofactorElement,
    QuadraticAlgebra.norm_def]
  ring

/-- The exponent-five ledger identity, with the cofactor displayed as a
golden-ring norm. -/
theorem quintic_ledger (a b : ℤ) :
    a ^ 5 + b ^ 5 =
      (a + b) * goldenNorm (quinticCofactorElement a b) := by
  rw [← quinticCofactor_eq_goldenNorm]
  simp only [quinticCofactor]
  ring

/-- A Fermat equation at exponent five becomes the conservation ledger
equation in the golden ring. -/
theorem fermatEquation_five_ledger {a b c : ℤ}
    (h : a ^ 5 + b ^ 5 = c ^ 5) :
    (a + b) * goldenNorm (quinticCofactorElement a b) = c ^ 5 := by
  rw [← quintic_ledger]
  exact h

/-- The ramified drain quantum `√5 = 2φ - 1` in `ℤ[φ]`. -/
def sqrtFiveDrainQuantum : GoldenInt :=
  ⟨-1, 2⟩

/-- The drain quantum really squares to the rational integer `5`. -/
theorem sqrtFiveDrainQuantum_sq :
    sqrtFiveDrainQuantum * sqrtFiveDrainQuantum = (5 : GoldenInt) := by
  ext <;>
    norm_num [sqrtFiveDrainQuantum, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat]

/-- The signed norm of the ramified drain quantum is `-5`. -/
theorem sqrtFiveDrainQuantum_norm :
    goldenNorm sqrtFiveDrainQuantum = -5 := by
  norm_num [goldenNorm, sqrtFiveDrainQuantum, QuadraticAlgebra.norm_def]

/-- The gauge-invariant charge removed by one `√5` drain is exactly `5`. -/
theorem sqrtFiveDrainQuantum_charge :
    goldenCharge sqrtFiveDrainQuantum = 5 := by
  rw [goldenCharge, sqrtFiveDrainQuantum_norm]
  decide

end Fermat.Five.Conservation
