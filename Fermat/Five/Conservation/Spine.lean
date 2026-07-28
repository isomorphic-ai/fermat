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

Write `φ` for a root of `φ² = φ + 1`.  The maximal golden order from
`Fermat.Quadratic.GoldenUnits` is the integral ring `ℤ[φ]`; its Pell
classification proves that every unit is, up to sign, a power of `φ`.
The norm of `x + yφ` is `x² + xy - y²`.
-/
import Fermat.Conservation.Floor
import Fermat.Quadratic.GoldenUnits
import Mathlib.Tactic.Ring

namespace Fermat.Five.Conservation

open Fermat.Quadratic.Golden

/-- The integral golden ring `ℤ[φ]`, presented by `φ² = φ + 1`. -/
abbrev GoldenInt := MaximalOrder

/-- The golden generator `φ`, with `φ² = φ + 1`. -/
abbrev goldenPhi : GoldenInt := MaximalOrder.phi

/-- The golden generator as a unit; its inverse is `φ - 1`. -/
abbrev goldenPhiUnit : GoldenIntˣ := MaximalOrder.phiUnit

@[simp] theorem coe_goldenPhiUnit :
    (goldenPhiUnit : GoldenInt) = goldenPhi :=
  rfl

/-- Distinct natural powers of `φ` are distinct units. -/
theorem goldenPhiUnit_pow_injective :
    Function.Injective (fun n : ℕ => goldenPhiUnit ^ n) := by
  intro m n h
  have hreal :=
    congrArg
      (fun u : GoldenIntˣ => MaximalOrder.toReal (u : GoldenInt))
      h
  simp only [Units.val_pow_eq_pow_val, coe_goldenPhiUnit, map_pow,
    MaximalOrder.toReal_phi] at hreal
  exact
    (pow_right_strictMono₀ Real.one_lt_goldenRatio).injective hreal

/-- The golden-ring unit group is infinite, witnessed by the powers of
`φ`.  These are the Pell/Dirichlet gauge transformations at exponent five. -/
theorem infinite_goldenUnitGroup : Infinite GoldenIntˣ :=
  Infinite.of_injective
    (fun n : ℕ => goldenPhiUnit ^ n)
    goldenPhiUnit_pow_injective

/-- The signed golden-ring norm `N(x + yφ) = x² + xy - y²`. -/
abbrev goldenNorm : GoldenInt →* ℤ := MaximalOrder.normMonoidHom

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
  exact u.isUnit.map goldenNorm

/-- A golden-ring unit carries exactly one unit of absolute norm charge. -/
theorem goldenCharge_unit (u : GoldenIntˣ) :
    goldenCharge (u : GoldenInt) = 1 := by
  exact MaximalOrder.natAbs_norm_eq_one_iff_isUnit.mpr u.isUnit

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
  change
    quinticCofactor a b =
      (a ^ 2 + b ^ 2) ^ 2 +
        (a ^ 2 + b ^ 2) * (-(a * b)) -
          (-(a * b)) ^ 2
  simp only [quinticCofactor]
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
  ext <;> norm_num [sqrtFiveDrainQuantum]

/-- The signed norm of the ramified drain quantum is `-5`. -/
theorem sqrtFiveDrainQuantum_norm :
    goldenNorm sqrtFiveDrainQuantum = -5 := by
  change (-1 : ℤ) ^ 2 + (-1) * 2 - 2 ^ 2 = -5
  norm_num

/-- The gauge-invariant charge removed by one `√5` drain is exactly `5`. -/
theorem sqrtFiveDrainQuantum_charge :
    goldenCharge sqrtFiveDrainQuantum = 5 := by
  rw [goldenCharge, sqrtFiveDrainQuantum_norm]
  decide

end Fermat.Five.Conservation
