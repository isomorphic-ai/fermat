/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# FLT(3): the conservation spine

This module realizes the four structural rungs of the exponent-three
conservation proof.

The bounded Mathlib roles are:

* `Fermat.Conservation.Floor` supplies the shared well-founded floor for
  positive natural charges;
* `Algebra.QuadraticAlgebra.Basic` supplies the coordinate ring
  `ℤ[ζ₃] = ℤ[ω]`, its multiplication, and its algebraic norm;
* `Tactic.NormNum` and `Tactic.Ring` discharge explicit integer polynomial
  identities only.

No fixed-exponent FLT theorem is imported.
-/
import Fermat.Conservation.Transfer
import Mathlib.Algebra.QuadraticAlgebra.Basic
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

private theorem cubic_factor_raw (a b : ℤ) :
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

/-- Ramified charge is monotone in its multiplicity.  This non-strict fact is
used only to type the before/after accounting states; strictness is projected
from the resulting positive transaction below. -/
theorem drainCharge_mono {m n : ℕ} (h : m ≤ n) :
    drainCharge m ≤ drainCharge n := by
  rw [drainCharge_eq, drainCharge_eq]
  exact Nat.pow_le_pow_right (by decide) h

/-- The state-linked cubic ledger at one ramified multiplicity.

The first coordinate is the drain stock.  The second coordinate is the cubic
factor `(a + b) * N(a + bζ₃)`.  Converted stock is measured against one fixed
budget, so successive states with that budget compose without resetting the
account. -/
def drainLedger (a b : ℤ) (budget multiplicity : ℕ)
    (hbudget : drainCharge multiplicity ≤ budget) :
    Fermat.Conservation.Ledger (ℕ × ℤ) where
  stock := (drainCharge multiplicity,
    (a + b) * charge (ofCoeffs a b))
  credit := (0, 0)
  converted := (budget - drainCharge multiplicity, 0)
  total := (budget, a ^ 3 + b ^ 3)
  conservation := by
    apply Prod.ext
    · simp only [Prod.fst_add]
      omega
    · simp only [Prod.snd_add, add_zero]
      exact (cubic_factor_raw a b).symm

/-- One state-linked ramified transaction.  The same before/after state
contains both the multiplicity charge and the cubic factor ledger. -/
def drainTransfer (a b : ℤ) (budget : ℕ) {m n : ℕ}
    (hmn : m ≤ n) (hbudget : drainCharge n ≤ budget) :
    Fermat.Conservation.Transfer (ℕ × ℤ) where
  before := drainLedger a b budget n hbudget
  after := drainLedger a b budget m
    (le_trans (drainCharge_mono hmn) hbudget)
  spent := (drainCharge n - drainCharge m, 0)
  before_conserved :=
    Fermat.Conservation.Ledger.conservation_identity _
  after_conserved :=
    Fermat.Conservation.Ledger.conservation_identity _
  total_preserved := rfl
  available_decomposition := by
    apply Prod.ext
    · simp only [drainLedger, Prod.fst_add, add_zero]
      have hcharge := drainCharge_mono hmn
      omega
    · simp only [drainLedger, Prod.snd_add, add_zero]
  converted_decomposition := by
    apply Prod.ext
    · simp only [drainLedger, Prod.fst_add]
      have hcharge := drainCharge_mono hmn
      omega
    · simp only [drainLedger, Prod.snd_add, add_zero]

/-- The factor ledger is the second-coordinate projection of the very same
transaction that carries the ramified stock. -/
theorem drainTransfer_factor_ledger (a b : ℤ) (budget : ℕ) {m n : ℕ}
    (hmn : m ≤ n) (hbudget : drainCharge n ≤ budget) :
    a ^ 3 + b ^ 3 = (a + b) * charge (ofCoeffs a b) := by
  have hconservation :=
    (drainTransfer a b budget hmn hbudget).endpoint_conservation.1
  have hfactor := congrArg Prod.snd hconservation
  simpa only [drainTransfer, drainLedger, Prod.snd_add, Prod.snd_zero,
    add_zero] using hfactor.symm

/-- **The cubic ledger.** The old factor identity is now a projection of an
accounted cubic state, rather than a parallel polynomial proof. -/
theorem ledger_identity (a b : ℤ) :
    a ^ 3 + b ^ 3 = (a + b) * charge (ofCoeffs a b) :=
  drainTransfer_factor_ledger a b (drainCharge 0)
    (m := 0) (n := 0) le_rfl le_rfl

/-- The first-coordinate stock decomposition of the cubic transaction. -/
theorem drainTransfer_stock_decomposition (a b : ℤ) (budget : ℕ)
    {m n : ℕ} (hmn : m ≤ n) (hbudget : drainCharge n ≤ budget) :
    drainCharge n = drainCharge m +
      (drainTransfer a b budget hmn hbudget).spent.1 := by
  have havailable := congrArg Prod.fst
    (drainTransfer a b budget hmn hbudget).available_eq
  simpa only [Fermat.Conservation.Transfer.available, drainTransfer,
    drainLedger, Prod.fst_add, add_zero] using havailable

/-- A strict multiplicity drop funds a positive accounted spend.  This is the
primitive positivity input; the legacy stock inequality is projected from it
and the transfer equation below. -/
theorem drainSpent_pos_of_multiplicity_lt {m n : ℕ} (h : m < n) :
    0 < drainCharge n - drainCharge m := by
  apply Nat.sub_pos_of_lt
  rw [drainCharge_eq, drainCharge_eq]
  exact Nat.pow_lt_pow_right (by norm_num) h

/-- Removing one drain quantum transfers charge strictly downward.  The
legacy inequality is the stock projection of a positive `drainTransfer`. -/
theorem drainCharge_pred_lt {m n : ℕ} (h : m < n) :
    drainCharge m < drainCharge n := by
  let transfer := drainTransfer 0 0 (drainCharge n) h.le le_rfl
  have hspent : 0 < transfer.spent.1 := by
    simpa only [transfer, drainTransfer] using
      drainSpent_pos_of_multiplicity_lt h
  rw [drainTransfer_stock_decomposition 0 0 (drainCharge n) h.le le_rfl]
  exact Nat.lt_add_of_pos_right hspent

end Fermat.Three.Conservation
