/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The exponent-59 conservation spine

This file is the literal structural composition boundary for the eighth
conservation rung.  It imports the proposition-only FLT statement and the
seven preceding conservation primitives, but no classical exponent-59 proof
and no generic irregular-prime machinery.

The new primitive is a three-column ledger

`stock + credit + converted = total`.

Repayment is an internal transfer from `credit` to `converted`, so it cannot
change the total.  This statement is deliberately generic: it says nothing
about whether a particular arithmetic credit draw can be repaid.

The conductor-specific portion specializes the generic N7 norm/gauge
primitive to a 59th cyclotomic field.  Its free unit rank is 28, and the
ramified quantum `1 - ζ₅₉` has charge 59.
-/
import Fermat.Statement.Basic
import Fermat.One.Conservation
import Fermat.Two.PythagorasConservation
import Fermat.Three.Conservation.Spine
import Fermat.Four.Conservation.Spine
import Fermat.Five.Conservation.Spine
import Fermat.Six.Conservation.Spine
import Fermat.Seven.Conservation.Spine

open scoped BigOperators NumberField

namespace Fermat.FiftyNine.Conservation

/-! ## The three-column conservation ledger -/

/-- A conservation ledger with explicit stock, credit, and converted
columns.  The equation is data: every ledger state carries its own audit. -/
structure Ledger (α : Type*) [AddCommMonoid α] where
  stock : α
  credit : α
  converted : α
  total : α
  conservation : stock + credit + converted = total

namespace Ledger

variable {α : Type*} [AddCommMonoid α]

/-- The empty ledger is the additive identity, mirroring the N1 vacuum. -/
def vacuum : Ledger α where
  stock := 0
  credit := 0
  converted := 0
  total := 0
  conservation := by simp

/-- Repay an explicitly decomposed credit amount by transferring it into the
converted column.  Requiring `credit = remaining + amount` makes the
operation valid without cancellation or subtraction assumptions. -/
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
      _ = ledger.total := ledger.conservation

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

/-- Repayment is a transfer internal to the ledger and therefore preserves
the audited total definitionally. -/
@[simp] theorem repay_total (ledger : Ledger α) (amount remaining : α)
    (hcredit : ledger.credit = remaining + amount) :
    (ledger.repay amount remaining hcredit).total = ledger.total :=
  rfl

/-- Natural-number repayment transfers any amount bounded by the available
credit. -/
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

/-- Bounded natural-number repayment preserves the total quantity. -/
@[simp] theorem repayNat_total (ledger : Ledger ℕ) (amount : ℕ)
    (hamount : amount ≤ ledger.credit) :
    (ledger.repayNat amount hamount).total = ledger.total :=
  rfl

end Ledger

/-! ## N59 adapters for the generic N7 charge and gauge -/

noncomputable section

open NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- The N59 charge is exactly the generic absolute integral norm charge
introduced by the N7 spine. -/
abbrev charge (z : 𝓞 K) : ℕ :=
  Fermat.Seven.Conservation.charge z

omit [NumberField K] in
/-- Multiplicative conservation is inherited literally from the N7
primitive. -/
theorem charge_mul (z w : 𝓞 K) :
    charge (z * w) = charge z * charge w :=
  Fermat.Seven.Conservation.charge_mul z w

/-- The complete free-coordinate family from the generic N7 gauge. -/
abbrev GaugeCoordinates (K : Type*) [Field K] [NumberField K] :=
  Fermat.Seven.Conservation.GaugeCoordinates K

/-- Torsion together with the complete free-coordinate family. -/
abbrev FullGaugeCoordinates (K : Type*) [Field K] [NumberField K] :=
  Fermat.Seven.Conservation.FullGaugeCoordinates K

/-- Evaluate a free gauge coordinate using the N7 fundamental system. -/
abbrev gaugeUnit (K : Type*) [Field K] [NumberField K]
    (coordinates : GaugeCoordinates K) : (𝓞 K)ˣ :=
  Fermat.Seven.Conservation.gaugeUnit K coordinates

/-- Evaluate torsion and free coordinates together. -/
abbrev fullGaugeUnit (K : Type*) [Field K] [NumberField K]
    (coordinates : FullGaugeCoordinates K) : (𝓞 K)ˣ :=
  Fermat.Seven.Conservation.fullGaugeUnit K coordinates

/-- The N7 unique Dirichlet decomposition, exposed at the N59 boundary. -/
theorem gauge_decomposition (u : (𝓞 K)ˣ) :
    ∃! coordinates : FullGaugeCoordinates K,
      u = fullGaugeUnit K coordinates :=
  Fermat.Seven.Conservation.gauge_decomposition u

/-- Every free rank-28 gauge transformation preserves norm charge. -/
theorem charge_gauge_invariant (coordinates : GaugeCoordinates K)
    (z : 𝓞 K) :
    charge ((gaugeUnit K coordinates : 𝓞 K) * z) = charge z :=
  Fermat.Seven.Conservation.charge_gauge_invariant coordinates z

/-- Torsion and all free coordinates together preserve norm charge. -/
theorem charge_full_gauge_invariant
    (coordinates : FullGaugeCoordinates K) (z : 𝓞 K) :
    charge ((fullGaugeUnit K coordinates : 𝓞 K) * z) = charge z :=
  Fermat.Seven.Conservation.charge_full_gauge_invariant coordinates z

/-- The free unit rank of a 59th cyclotomic field is 28. -/
theorem unitRank_eq_twentyEight [IsCyclotomicExtension {59} ℚ K] :
    NumberField.Units.rank K = 28 := by
  rw [NumberField.Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero K (n := 59) (by norm_num),
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two
      (K := K) 59]
  decide

/-- The abstract N7 gauge coordinates become a 28-entry integer vector at
conductor 59. -/
def gaugeCoordinatesEquiv [IsCyclotomicExtension {59} ℚ K] :
    GaugeCoordinates K ≃ (Fin 28 → ℤ) := by
  simpa only [GaugeCoordinates,
    Fermat.Seven.Conservation.GaugeCoordinates,
    unitRank_eq_twentyEight (K := K)] using
      (Equiv.refl (Fin 28 → ℤ))

/-- The N7 regulator, now governing a rank-28 gauge lattice. -/
abbrev gaugeRegulator (K : Type*) [Field K] [NumberField K] : ℝ :=
  Fermat.Seven.Conservation.gaugeRegulator K

/-- The conductor-59 gauge has rank 28 and positive regulator. -/
theorem rankTwentyEightGauge_regulator
    [IsCyclotomicExtension {59} ℚ K] :
    NumberField.Units.rank K = 28 ∧ 0 < gaugeRegulator K :=
  ⟨unitRank_eq_twentyEight,
    Fermat.Seven.Conservation.gaugeRegulator_pos⟩

/-! ## The conductor-59 ramified drain -/

section CyclotomicFiftyNine

variable [IsCyclotomicExtension {59} ℚ K]
variable {ζ : K}

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

/-- The ramified quantum `λ = 1 - ζ₅₉`. -/
def lambda (hζ : IsPrimitiveRoot ζ 59) : 𝓞 K :=
  1 - hζ.toInteger

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
/-- The requested orientation differs from `ζ₅₉ - 1` only by the unit
`-1`. -/
theorem lambda_eq_neg_zeta_sub_one (hζ : IsPrimitiveRoot ζ 59) :
    lambda hζ = -(hζ.toInteger - 1) := by
  simp only [lambda]
  ring

/-- One ramified quantum has absolute norm charge exactly 59. -/
theorem lambda_charge (hζ : IsPrimitiveRoot ζ 59) :
    charge (lambda hζ) = 59 := by
  rw [lambda_eq_neg_zeta_sub_one]
  rw [show -(hζ.toInteger - 1) =
      (-1 : 𝓞 K) * (hζ.toInteger - 1) by ring, charge_mul]
  have hneg : charge (-1 : 𝓞 K) = 1 := by
    simpa using
      Fermat.Seven.Conservation.charge_unit (K := K)
        (-1 : (𝓞 K)ˣ)
  rw [hneg, one_mul]
  simp only [charge, Fermat.Seven.Conservation.charge]
  rw [hζ.norm_toInteger_sub_one_of_prime_ne_two' (by norm_num)]
  norm_num

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
/-- Absolute norm charge is multiplicative on powers. -/
theorem charge_pow (z : 𝓞 K) (n : ℕ) :
    charge (z ^ n) = charge z ^ n :=
  Fermat.Seven.Conservation.charge_pow z n

/-- The charge stored in `n` ramified quanta. -/
def drainCharge (hζ : IsPrimitiveRoot ζ 59) (n : ℕ) : ℕ :=
  charge ((lambda hζ) ^ n)

/-- `n` ramified quanta carry literal charge `59 ^ n`. -/
theorem drainCharge_eq (hζ : IsPrimitiveRoot ζ 59) (n : ℕ) :
    drainCharge hζ n = 59 ^ n := by
  rw [drainCharge, charge_pow, lambda_charge]

/-- Ramified charge is strictly increasing with multiplicity; lowering
multiplicity is therefore a strict drain. -/
theorem drainCharge_strictMono (hζ : IsPrimitiveRoot ζ 59) :
    StrictMono (drainCharge hζ) := by
  intro m n hmn
  rw [drainCharge_eq, drainCharge_eq]
  exact Nat.pow_lt_pow_right (by norm_num) hmn

/-- Removing one ramified factor strictly lowers the associated charge. -/
theorem drainCharge_step (hζ : IsPrimitiveRoot ζ 59) (n : ℕ) :
    drainCharge hζ n < drainCharge hζ (n + 1) :=
  drainCharge_strictMono hζ (Nat.lt_succ_self n)

end CyclotomicFiftyNine

end

end Fermat.FiftyNine.Conservation
