/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# FLT(3): the conservation spine

This module realizes the four structural rungs of the exponent-three
conservation proof.

The bounded Mathlib roles are:

* `Algebra.QuadraticAlgebra.Basic` supplies the coordinate ring
  `ℤ[ζ₃] = ℤ[ω]`, its multiplication, and its algebraic norm;
* `Order.WellFounded` supplies the well-founded floor for natural charges;
* `Tactic.NormNum` and `Tactic.Ring` discharge explicit integer polynomial
  identities only.

No fixed-exponent FLT theorem is imported.
-/
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Order.WellFounded
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Fermat.Three.Conservation

/-- The Eisenstein integers, presented as
`ℤ[ω] = ℤ[X] / (X² + X + 1)`. -/
abbrev EisensteinInt := QuadraticAlgebra ℤ (-1) (-1)

/-- The distinguished primitive cube root `ζ₃`, represented by `ω`. -/
def zeta : EisensteinInt := QuadraticAlgebra.omega

/-- The Eisenstein integer `x + yζ₃`. -/
def ofCoeffs (x y : ℤ) : EisensteinInt := ⟨x, y⟩

/-- The conserved **charge** on `ℤ[ζ₃]`: its algebraic norm. -/
def charge (z : EisensteinInt) : ℤ := QuadraticAlgebra.norm z

/-- In coordinates, the charge is `N(x + yζ₃) = x² - xy + y²`. -/
theorem charge_formula (x y : ℤ) :
    charge (ofCoeffs x y) = x ^ 2 - x * y + y ^ 2 := by
  simp [charge, ofCoeffs, QuadraticAlgebra.norm_def]
  ring

/-- **Multiplicative conservation.** Eisenstein multiplication preserves the
charge ledger: `N(uv) = N(u)N(v)`. -/
theorem charge_mul (u v : EisensteinInt) :
    charge (u * v) = charge u * charge v := by
  exact map_mul QuadraticAlgebra.norm u v

/-- **The cubic ledger.** The integer Fermat equation factors as the sum
channel times Eisenstein charge. -/
theorem ledger_identity (a b : ℤ) :
    a ^ 3 + b ^ 3 = (a + b) * charge (ofCoeffs a b) := by
  rw [charge_formula]
  ring

/-- The drain unit `λ = 1 - ζ₃`. -/
def drainUnit : EisensteinInt := 1 - zeta

/-- The drain quantum carries exactly three units of charge: `N(λ) = 3`. -/
theorem drainUnit_charge : charge drainUnit = 3 := by
  have hlam : drainUnit = ofCoeffs 1 (-1) := rfl
  rw [hlam, charge_formula]
  norm_num

/-- Conservation iterated through powers:
`N(uⁿ) = N(u)ⁿ`. -/
theorem charge_pow (u : EisensteinInt) (n : ℕ) :
    charge (u ^ n) = charge u ^ n := by
  exact map_pow QuadraticAlgebra.norm u n

/-- The positive charge stored in `n` drain quanta. -/
def drainCharge (n : ℕ) : ℕ :=
  (charge (drainUnit ^ n)).natAbs

/-- `n` drain quanta carry charge `3ⁿ`. -/
theorem drainCharge_eq (n : ℕ) : drainCharge n = 3 ^ n := by
  simp [drainCharge, charge_pow, drainUnit_charge]

/-- Removing one drain quantum transfers charge strictly downward. -/
theorem drainCharge_pred_lt {m n : ℕ} (h : m < n) :
    drainCharge m < drainCharge n := by
  rw [drainCharge_eq, drainCharge_eq]
  exact Nat.pow_lt_pow_right (by norm_num) h

/-- **The conservation floor.** There is no infinite sequence of positive
natural charges that drops strictly at every successor. -/
theorem noInfinitePositiveChargeDrain :
    ¬ ∃ q : ℕ → ℕ, (∀ n, 0 < q n) ∧ ∀ n, q (n + 1) < q n := by
  rintro ⟨q, -, hdrop⟩
  obtain ⟨n, hn⟩ :=
    WellFounded.not_rel_apply_succ (r := (· < ·)) q
  exact hn (hdrop n)

end Fermat.Three.Conservation
