/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Accounted transfers

A `Transfer` is the route-neutral transaction underlying the older strict
charge vocabulary.  It records two literal three-column ledger states and the
single amount moved out of their combined spendable columns and into the
converted column.  An exact additive decomposition is used instead of
subtraction, so the core works over every additive commutative monoid and still
permits neutral rerouting between stock and credit.

Transfers compose.  Over `ℕ`, a positive transfer strictly lowers the sum of
the stock and credit columns; an iterable path of positive transfers therefore
supplies exactly the `hstep` consumed by the existing conservation floor.
-/
import Fermat.Conservation.Floor
import Fermat.Conservation.Ledger

namespace Fermat.Conservation

/-- An accounted transaction between two ledger states over one carrier.

The combined stock-plus-credit delta is the route-neutral `spent`, and
precisely that amount is added to `converted` while `total` is preserved.
Concrete adapters may additionally show that stock or credit is fixed; those
are projections of the transaction, not restrictions on the common core. -/
structure Transfer (α : Type*) [AddCommMonoid α] where
  before : Ledger α
  after : Ledger α
  spent : α
  before_conserved :
    before.stock + before.credit + before.converted = before.total
  after_conserved :
    after.stock + after.credit + after.converted = after.total
  total_preserved : before.total = after.total
  available_decomposition :
    before.stock + before.credit = after.stock + after.credit + spent
  converted_decomposition : after.converted = before.converted + spent

namespace Transfer

variable {α : Type*} [AddCommMonoid α]

/-- The spendable part of a ledger, before it is moved to `converted`. -/
def available (ledger : Ledger α) : α :=
  ledger.stock + ledger.credit

/-- Both endpoints use the named global conservation identity. -/
theorem endpoint_conservation (transfer : Transfer α) :
    (transfer.before.stock + transfer.before.credit +
        transfer.before.converted = transfer.before.total) ∧
      (transfer.after.stock + transfer.after.credit +
        transfer.after.converted = transfer.after.total) :=
  ⟨Ledger.conservation_identity transfer.before,
    Ledger.conservation_identity transfer.after⟩

/-- The structure's exact column equation in named spendable form. -/
theorem available_eq (transfer : Transfer α) :
    available transfer.before = available transfer.after + transfer.spent := by
  simpa only [available, add_assoc] using transfer.available_decomposition

/-- A zero transaction at one ledger state. -/
def refl (ledger : Ledger α) : Transfer α where
  before := ledger
  after := ledger
  spent := 0
  before_conserved := Ledger.conservation_identity ledger
  after_conserved := Ledger.conservation_identity ledger
  total_preserved := rfl
  available_decomposition := by simp
  converted_decomposition := by simp

/-- Compose consecutive transactions.  The intermediate ledger is supplied as
an equality because `Transfer` keeps its endpoints as data rather than type
indices. -/
def comp (first second : Transfer α)
    (hlink : first.after = second.before) : Transfer α where
  before := first.before
  after := second.after
  spent := first.spent + second.spent
  before_conserved := Ledger.conservation_identity first.before
  after_conserved := Ledger.conservation_identity second.after
  total_preserved := by
    calc
      first.before.total = first.after.total := first.total_preserved
      _ = second.before.total := by rw [hlink]
      _ = second.after.total := second.total_preserved
  available_decomposition := by
    calc
      first.before.stock + first.before.credit =
          first.after.stock + first.after.credit + first.spent :=
        first.available_decomposition
      _ = second.before.stock + second.before.credit + first.spent := by
        rw [hlink]
      _ = (second.after.stock + second.after.credit + second.spent) +
          first.spent := by
        rw [second.available_decomposition]
      _ = second.after.stock + second.after.credit +
          (first.spent + second.spent) := by
        ac_rfl
  converted_decomposition := by
    calc
      second.after.converted = second.before.converted + second.spent :=
        second.converted_decomposition
      _ = first.after.converted + second.spent := by rw [← hlink]
      _ = (first.before.converted + first.spent) + second.spent := by
        rw [first.converted_decomposition]
      _ = first.before.converted + (first.spent + second.spent) := by
        ac_rfl

/-- The literal ledger repayment operation, exposed as its accounted
transaction rather than only as a post-state. -/
def ofRepay (ledger : Ledger α) (amount remaining : α)
    (hcredit : ledger.credit = remaining + amount) : Transfer α where
  before := ledger
  after := ledger.repay amount remaining hcredit
  spent := amount
  before_conserved := Ledger.conservation_identity ledger
  after_conserved := Ledger.conservation_identity
    (ledger.repay amount remaining hcredit)
  total_preserved := rfl
  available_decomposition := by
    rw [Ledger.repay_stock, Ledger.repay_credit, hcredit]
    ac_rfl
  converted_decomposition := rfl

/-- Bounded natural-number repayment as a transaction. -/
def ofRepayNat (ledger : Ledger ℕ) (amount : ℕ)
    (hamount : amount ≤ ledger.credit) : Transfer ℕ :=
  ofRepay ledger amount (ledger.credit - amount)
    (Nat.sub_add_cancel hamount).symm

/-- Positive spending is exactly the legacy strict spendable-charge drop. -/
theorem available_lt_of_spent_pos (transfer : Transfer ℕ)
    (hspent : 0 < transfer.spent) :
    available transfer.after < available transfer.before := by
  rw [transfer.available_eq]
  exact Nat.lt_add_of_pos_right hspent

/-- If credit is merely rerouted unchanged, the aggregate equation identifies
the entire spend with the stock-column decrease. -/
theorem stock_decomposition_of_credit_eq (transfer : Transfer ℕ)
    (hcredit : transfer.before.credit = transfer.after.credit) :
    transfer.before.stock = transfer.after.stock + transfer.spent := by
  have h := transfer.available_decomposition
  omega

/-- If stock is fixed, the aggregate equation identifies the entire spend
with the credit-column decrease. -/
theorem credit_decomposition_of_stock_eq (transfer : Transfer ℕ)
    (hstock : transfer.before.stock = transfer.after.stock) :
    transfer.before.credit = transfer.after.credit + transfer.spent := by
  have h := transfer.available_decomposition
  omega

/-- A positive transfer with fixed credit strictly lowers stock. -/
theorem stock_lt_of_credit_eq (transfer : Transfer ℕ)
    (hcredit : transfer.before.credit = transfer.after.credit)
    (hspent : 0 < transfer.spent) :
    transfer.after.stock < transfer.before.stock := by
  rw [transfer.stock_decomposition_of_credit_eq hcredit]
  exact Nat.lt_add_of_pos_right hspent

/-- A positive transfer with fixed stock strictly lowers credit. -/
theorem credit_lt_of_stock_eq (transfer : Transfer ℕ)
    (hstock : transfer.before.stock = transfer.after.stock)
    (hspent : 0 < transfer.spent) :
    transfer.after.credit < transfer.before.credit := by
  rw [transfer.credit_decomposition_of_stock_eq hstock]
  exact Nat.lt_add_of_pos_right hspent

/-- A positive accounted step between client states. -/
def PositiveStep {σ : Type*} (account : σ → Ledger ℕ)
    (state next : σ) : Prop :=
  ∃ transfer : Transfer ℕ,
    transfer.before = account state ∧
      transfer.after = account next ∧ 0 < transfer.spent

/-- A chain of positive accounted steps projects to the exact strict `hstep`
shape consumed by `impossible_of_strict_charge_drain`. -/
theorem floor_hstep_of_positiveSteps {σ : Type*}
    (account : σ → Ledger ℕ)
    (htransfer : ∀ state, ∃ next, PositiveStep account state next) :
    ∀ state, ∃ next,
      available (account next) < available (account state) := by
  intro state
  obtain ⟨next, transfer, hbefore, hafter, hspent⟩ := htransfer state
  refine ⟨next, ?_⟩
  rw [← hbefore, ← hafter]
  exact transfer.available_lt_of_spent_pos hspent

/-- The conservation floor, with its old strict premise derived from an
iterable path of positive transactions. -/
theorem impossible_of_positive_transfer_drain {σ : Type*}
    (start : σ) (account : σ → Ledger ℕ)
    (hpositive : ∀ state, 0 < available (account state))
    (htransfer : ∀ state, ∃ next, PositiveStep account state next) :
    False :=
  impossible_of_strict_charge_drain start (available ∘ account) hpositive
    (floor_hstep_of_positiveSteps account htransfer)

end Transfer

end Fermat.Conservation
