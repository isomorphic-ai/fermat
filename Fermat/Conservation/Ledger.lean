/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The literal three-column conservation ledger

This is an accounting carrier, not a replacement for the generated
set-valued credit matrix.  A concrete cone may map its native stock, credit,
and conversion objects into any common additive carrier `α`; only after such
a map is supplied does the literal equation below apply.
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat.Defs

namespace Fermat.Conservation

/-- A three-column ledger whose audit equation is carried with the state. -/
structure Ledger (α : Type*) [AddCommMonoid α] where
  stock : α
  credit : α
  converted : α
  total : α
  conservation : stock + credit + converted = total

namespace Ledger

variable {α : Type*} [AddCommMonoid α]

/-- The named global conservation identity audited by `#guard_depends_on`. -/
theorem conservation_identity (ledger : Ledger α) :
    ledger.stock + ledger.credit + ledger.converted = ledger.total :=
  ledger.conservation

/-- The empty accounting state.  Native C1 vacuum objects can map here once
their contribution to the common carrier is proved to be zero. -/
def vacuum : Ledger α where
  stock := 0
  credit := 0
  converted := 0
  total := 0
  conservation := by simp

/-- The vacuum state literally satisfies the three-column identity. -/
theorem vacuum_conservation :
    (vacuum : Ledger α).stock + vacuum.credit + vacuum.converted =
      vacuum.total :=
  conservation_identity vacuum

/-- Transfer one explicitly decomposed credit amount into the converted
column.  The generated credit object itself is not coerced to a scalar by
this operation; callers must first provide an honest additive accounting
map and the displayed decomposition in its codomain. -/
def repay (ledger : Ledger α) (amount remaining : α)
    (hcredit : ledger.credit = remaining + amount) : Ledger α where
  stock := ledger.stock
  credit := remaining
  converted := ledger.converted + amount
  total := ledger.total
  conservation := by
    calc
      ledger.stock + remaining + (ledger.converted + amount) =
          ledger.stock + (remaining + amount) + ledger.converted := by
            ac_rfl
      _ = ledger.stock + ledger.credit + ledger.converted := by
            rw [← hcredit]
      _ = ledger.total := conservation_identity ledger

@[simp] theorem repay_stock (ledger : Ledger α) (amount remaining : α)
    (hcredit : ledger.credit = remaining + amount) :
    (ledger.repay amount remaining hcredit).stock = ledger.stock :=
  rfl

@[simp] theorem repay_credit (ledger : Ledger α) (amount remaining : α)
    (hcredit : ledger.credit = remaining + amount) :
    (ledger.repay amount remaining hcredit).credit = remaining :=
  rfl

@[simp] theorem repay_converted (ledger : Ledger α) (amount remaining : α)
    (hcredit : ledger.credit = remaining + amount) :
    (ledger.repay amount remaining hcredit).converted =
      ledger.converted + amount :=
  rfl

@[simp] theorem repay_total (ledger : Ledger α) (amount remaining : α)
    (hcredit : ledger.credit = remaining + amount) :
    (ledger.repay amount remaining hcredit).total = ledger.total :=
  rfl

/-- The post-transfer state still satisfies the same literal identity. -/
theorem repay_conservation (ledger : Ledger α) (amount remaining : α)
    (hcredit : ledger.credit = remaining + amount) :
    (ledger.repay amount remaining hcredit).stock +
        (ledger.repay amount remaining hcredit).credit +
        (ledger.repay amount remaining hcredit).converted =
      (ledger.repay amount remaining hcredit).total :=
  conservation_identity (ledger.repay amount remaining hcredit)

/-- Natural-number repayment transfers any amount bounded by available
accounted credit. -/
def repayNat (ledger : Ledger ℕ) (amount : ℕ)
    (hamount : amount ≤ ledger.credit) : Ledger ℕ :=
  ledger.repay amount (ledger.credit - amount)
    (Nat.sub_add_cancel hamount).symm

@[simp] theorem repayNat_credit (ledger : Ledger ℕ) (amount : ℕ)
    (hamount : amount ≤ ledger.credit) :
    (ledger.repayNat amount hamount).credit = ledger.credit - amount :=
  rfl

@[simp] theorem repayNat_converted (ledger : Ledger ℕ) (amount : ℕ)
    (hamount : amount ≤ ledger.credit) :
    (ledger.repayNat amount hamount).converted =
      ledger.converted + amount :=
  rfl

@[simp] theorem repayNat_total (ledger : Ledger ℕ) (amount : ℕ)
    (hamount : amount ≤ ledger.credit) :
    (ledger.repayNat amount hamount).total = ledger.total :=
  rfl

/-- Bounded natural-number repayment retains the literal audit equation. -/
theorem repayNat_conservation (ledger : Ledger ℕ) (amount : ℕ)
    (hamount : amount ≤ ledger.credit) :
    (ledger.repayNat amount hamount).stock +
        (ledger.repayNat amount hamount).credit +
        (ledger.repayNat amount hamount).converted =
      (ledger.repayNat amount hamount).total :=
  conservation_identity (ledger.repayNat amount hamount)

end Ledger

end Fermat.Conservation
