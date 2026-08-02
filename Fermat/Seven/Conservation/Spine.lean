/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The seventh-cyclotomic conservation spine

This file supplies the algebraic vocabulary used by the conservation proof
at exponent seven.  It deliberately uses only Mathlib's cyclotomic and
Dirichlet-unit APIs together with the shared conservation floor; in
particular, it imports no earlier implementation under `Fermat.Seven`.

The septic polynomial identity is reconstructed from the historical folding
notes in this repository.  The key new feature at exponent seven is that the
free unit quotient has rank two.  Consequently a gauge representative has
two integer coordinates, while a complete unit decomposition also retains
its torsion coordinate.  Mathlib's regulator is the covolume of precisely
this full unit lattice.
-/
import Fermat.Conservation.Floor
import Fermat.Conservation.Transfer
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators NumberField

namespace Fermat.Seven.Conservation

noncomputable section

open NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-! ## Absolute integral norm charge -/

/-- The nonnegative conservation charge on the ring of integers: absolute
field norm to `ℤ`. -/
def charge (z : 𝓞 K) : ℕ :=
  (Algebra.norm ℤ z).natAbs

omit [NumberField K] in
/-- The absolute integral norm charge is multiplicative. -/
theorem charge_mul (z w : 𝓞 K) :
    charge (z * w) = charge z * charge w := by
  simp only [charge, map_mul, Int.natAbs_mul]

omit [NumberField K] in
/-- The integral norm of a unit is `1` or `-1`. -/
theorem norm_unit_eq_one_or_neg_one (u : (𝓞 K)ˣ) :
    Algebra.norm ℤ (u : 𝓞 K) = 1 ∨
      Algebra.norm ℤ (u : 𝓞 K) = -1 := by
  apply Int.isUnit_eq_one_or
  exact u.isUnit.map (Algebra.norm ℤ)

omit [NumberField K] in
/-- Every unit carries exactly one unit of absolute norm charge. -/
theorem charge_unit (u : (𝓞 K)ˣ) :
    charge (u : 𝓞 K) = 1 := by
  rcases norm_unit_eq_one_or_neg_one u with h | h
  · simp [charge, h]
  · simp [charge, h]

omit [NumberField K] in
/-- Multiplication by an arbitrary ambient unit preserves the charge. -/
theorem charge_unit_invariant (u : (𝓞 K)ˣ) (z : 𝓞 K) :
    charge ((u : 𝓞 K) * z) = charge z := by
  rw [charge_mul, charge_unit, one_mul]

/-! ## The full rank-two Dirichlet gauge -/

/-- Integer coordinates on the free part of the full unit group. -/
abbrev GaugeCoordinates (K : Type*) [Field K] [NumberField K] :=
  Fin (NumberField.Units.rank K) → ℤ

/-- The unit represented by all fundamental-system coordinates. -/
def gaugeUnit (K : Type*) [Field K] [NumberField K]
    (e : GaugeCoordinates K) : (𝓞 K)ˣ :=
  ∏ i, (NumberField.Units.fundSystem K i) ^ (e i)

/-- A complete gauge coordinate consists of torsion together with all free
Dirichlet coordinates. -/
abbrev FullGaugeCoordinates (K : Type*) [Field K] [NumberField K] :=
  NumberField.Units.torsion K × GaugeCoordinates K

/-- Evaluation of a full gauge coordinate, including its torsion factor. -/
def fullGaugeUnit (K : Type*) [Field K] [NumberField K]
    (coordinates : FullGaugeCoordinates K) : (𝓞 K)ˣ :=
  coordinates.1 * gaugeUnit K coordinates.2

/-- A supplied complete unit decomposition as a literal global account.
The additive wrapper turns multiplication in the unit group into the
additive carrier expected by `Ledger`. -/
def gaugeAccountLedger (u : (𝓞 K)ˣ)
    (coordinates : FullGaugeCoordinates K)
    (hcoordinates : u = fullGaugeUnit K coordinates) :
    Fermat.Conservation.Ledger (Additive (𝓞 K)ˣ) where
  stock := Additive.ofMul (fullGaugeUnit K coordinates)
  credit := 0
  converted := 0
  total := Additive.ofMul u
  conservation := by
    simpa only [add_zero] using congrArg Additive.ofMul hcoordinates.symm

/-- Every unit has a unique decomposition into a torsion unit and powers of
the complete Dirichlet fundamental system. -/
theorem gauge_decomposition (u : (𝓞 K)ˣ) :
    ∃! coordinates : FullGaugeCoordinates K,
      u = fullGaugeUnit K coordinates := by
  have hraw :
      ∃! coordinates : FullGaugeCoordinates K,
        u = fullGaugeUnit K coordinates := by
    simpa only [FullGaugeCoordinates, fullGaugeUnit, gaugeUnit] using
      NumberField.Units.exist_unique_eq_mul_prod K u
  obtain ⟨coordinates, hcoordinates, hunique⟩ := hraw
  refine ⟨coordinates, ?_, hunique⟩
  have hconservation :=
    Fermat.Conservation.Ledger.conservation_identity
      (gaugeAccountLedger u coordinates hcoordinates)
  simp only [gaugeAccountLedger, add_zero] at hconservation
  exact congrArg Additive.toMul hconservation.symm

/-- The free unit rank of a seventh cyclotomic field is exactly two. -/
theorem unitRank_eq_two [IsCyclotomicExtension {7} ℚ K] :
    NumberField.Units.rank K = 2 := by
  rw [NumberField.Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero K (n := 7) (by norm_num),
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (K := K) 7]
  decide

/-- The abstract fundamental-system coordinates are concretely two integer
coordinates in a seventh cyclotomic field. -/
def gaugeCoordinatesEquiv [IsCyclotomicExtension {7} ℚ K] :
    GaugeCoordinates K ≃ ℤ × ℤ := by
  simpa only [GaugeCoordinates, unitRank_eq_two (K := K)] using
    finTwoArrowEquiv ℤ

private theorem charge_gauge_invariant_raw
    (e : GaugeCoordinates K) (z : 𝓞 K) :
    charge ((gaugeUnit K e : 𝓞 K) * z) = charge z :=
  charge_unit_invariant (gaugeUnit K e) z

private theorem charge_full_gauge_invariant_raw
    (coordinates : FullGaugeCoordinates K) (z : 𝓞 K) :
    charge ((fullGaugeUnit K coordinates : 𝓞 K) * z) = charge z :=
  charge_unit_invariant (fullGaugeUnit K coordinates) z

/-- A seventh-cyclotomic charge under one fixed accounting budget. -/
def chargeLedger (budget : ℕ) (z : 𝓞 K)
    (hbudget : charge z ≤ budget) :
    Fermat.Conservation.Ledger ℕ where
  stock := charge z
  credit := 0
  converted := budget - charge z
  total := budget
  conservation := by omega

/-- A free rank-two gauge step as a zero-spent transaction preserving all
four global columns. -/
def gaugeTransfer (budget : ℕ) (e : GaugeCoordinates K) (z : 𝓞 K)
    (hbudget : charge z ≤ budget) :
    Fermat.Conservation.Transfer ℕ where
  before := chargeLedger budget z hbudget
  after := chargeLedger budget ((gaugeUnit K e : 𝓞 K) * z) (by
    rw [charge_gauge_invariant_raw]
    exact hbudget)
  spent := 0
  before_conserved :=
    Fermat.Conservation.Ledger.conservation_identity _
  after_conserved :=
    Fermat.Conservation.Ledger.conservation_identity _
  total_preserved := rfl
  available_decomposition := by
    simp only [chargeLedger, add_zero]
    exact (charge_gauge_invariant_raw e z).symm
  converted_decomposition := by
    simp only [chargeLedger, add_zero]
    rw [charge_gauge_invariant_raw]

/-- A full torsion-plus-free gauge step as the corresponding zero-spent
transaction. -/
def fullGaugeTransfer (budget : ℕ)
    (coordinates : FullGaugeCoordinates K) (z : 𝓞 K)
    (hbudget : charge z ≤ budget) :
    Fermat.Conservation.Transfer ℕ where
  before := chargeLedger budget z hbudget
  after := chargeLedger budget
    ((fullGaugeUnit K coordinates : 𝓞 K) * z) (by
      rw [charge_full_gauge_invariant_raw]
      exact hbudget)
  spent := 0
  before_conserved :=
    Fermat.Conservation.Ledger.conservation_identity _
  after_conserved :=
    Fermat.Conservation.Ledger.conservation_identity _
  total_preserved := rfl
  available_decomposition := by
    simp only [chargeLedger, add_zero]
    exact (charge_full_gauge_invariant_raw coordinates z).symm
  converted_decomposition := by
    simp only [chargeLedger, add_zero]
    rw [charge_full_gauge_invariant_raw]

/-- **Rank-two gauge invariance.** The legacy scalar equality is the stock
projection of the zero-spent gauge transaction. -/
theorem charge_gauge_invariant (e : GaugeCoordinates K) (z : 𝓞 K) :
    charge ((gaugeUnit K e : 𝓞 K) * z) = charge z := by
  have havailable :=
    (gaugeTransfer (charge z) e z le_rfl).available_eq
  symm
  simpa only [Fermat.Conservation.Transfer.available, gaugeTransfer,
    chargeLedger, add_zero] using havailable

/-- Torsion and both free coordinates together still leave charge unchanged,
as the same stock projection for the full-gauge transaction. -/
theorem charge_full_gauge_invariant
    (coordinates : FullGaugeCoordinates K) (z : 𝓞 K) :
    charge ((fullGaugeUnit K coordinates : 𝓞 K) * z) = charge z := by
  have havailable :=
    (fullGaugeTransfer (charge z) coordinates z le_rfl).available_eq
  symm
  simpa only [Fermat.Conservation.Transfer.available, fullGaugeTransfer,
    chargeLedger, add_zero] using havailable

/-! ## Regulator vocabulary -/

/-- The regulator governing the fundamental domain of the unit gauge
lattice.  In Mathlib this is the covolume of the unit lattice. -/
abbrev gaugeRegulator (K : Type*) [Field K] [NumberField K] : ℝ :=
  NumberField.Units.regulator K

/-- The chosen Dirichlet fundamental system has maximal rank. -/
theorem fundSystem_isMaxRank :
    NumberField.Units.IsMaxRank (NumberField.Units.fundSystem K) :=
  NumberField.Units.isMaxRank_fundSystem K

/-- The gauge regulator is the regulator of the complete fundamental
system. -/
theorem gaugeRegulator_eq_fundSystem :
    gaugeRegulator K =
      NumberField.Units.regOfFamily (NumberField.Units.fundSystem K) :=
  NumberField.Units.regulator_eq_regOfFamily_fundSystem K

/-- The gauge regulator is strictly positive. -/
theorem gaugeRegulator_pos :
    0 < gaugeRegulator K :=
  NumberField.Units.regulator_pos K

/-- At conductor seven, the two-dimensional gauge lattice has positive
regulator. -/
theorem rankTwoGauge_regulator
    [IsCyclotomicExtension {7} ℚ K] :
    NumberField.Units.rank K = 2 ∧ 0 < gaugeRegulator K :=
  ⟨unitRank_eq_two, gaugeRegulator_pos⟩

/-! ## The septic ledger -/

/-- The quadratic form occurring in the septic fold. -/
def septicC (x y : ℤ) : ℤ :=
  x ^ 2 - x * y + y ^ 2

/-- The historical all-positive septic fold polynomial. -/
def psiSeven (x y : ℤ) : ℤ :=
  x ^ 6 + x ^ 5 * y + x ^ 4 * y ^ 2 + x ^ 3 * y ^ 3 +
    x ^ 2 * y ^ 4 + x * y ^ 5 + y ^ 6

/-- The campaign's compressed septic fold identity. -/
theorem psiSeven_compressed (x y : ℤ) :
    psiSeven x y =
      (x - y) ^ 6 + 7 * x * y * (septicC x y) ^ 2 := by
  simp only [psiSeven, septicC]
  ring

/-- The all-positive fold is the quotient in the difference of seventh
powers. -/
theorem psiSeven_difference (x y : ℤ) :
    x ^ 7 - y ^ 7 = (x - y) * psiSeven x y := by
  simp only [psiSeven]
  ring

/-- The sign substitution needed for the sum ledger, in compressed form. -/
theorem psiSeven_neg_compressed (a b : ℤ) :
    psiSeven a (-b) =
      (a + b) ^ 6 -
        7 * a * b * (a ^ 2 + a * b + b ^ 2) ^ 2 := by
  simp only [psiSeven]
  ring

/-- The septic factorization as a literal global accounting state. -/
def septicAccountLedger (a b : ℤ) :
    Fermat.Conservation.Ledger ℤ where
  stock := (a + b) * psiSeven a (-b)
  credit := 0
  converted := 0
  total := a ^ 7 + b ^ 7
  conservation := by
    simp only [psiSeven]
    ring

/-- The exact septic conservation ledger for a sum of seventh powers, now
the stock/total projection of its global account. -/
theorem septic_ledger (a b : ℤ) :
    a ^ 7 + b ^ 7 = (a + b) * psiSeven a (-b) := by
  have hconservation :=
    Fermat.Conservation.Ledger.conservation_identity
      (septicAccountLedger a b)
  simpa only [septicAccountLedger, add_zero] using hconservation.symm

/-! ## The ramified drain quantum -/

section CyclotomicSeven

variable [IsCyclotomicExtension {7} ℚ K]
variable {ζ : K}

local instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-- The seventh-cyclotomic ramified element `λ = 1 - ζ₇`. -/
def lambda (hζ : IsPrimitiveRoot ζ 7) : 𝓞 K :=
  1 - hζ.toInteger

omit [NumberField K] [IsCyclotomicExtension {7} ℚ K] in
/-- The requested orientation of `λ` differs from `ζ₇ - 1` by the unit
`-1`. -/
theorem lambda_eq_neg_zeta_sub_one (hζ : IsPrimitiveRoot ζ 7) :
    lambda hζ = -(hζ.toInteger - 1) := by
  simp only [lambda]
  ring

/-- The drain quantum has absolute integral norm charge exactly seven. -/
theorem lambda_charge (hζ : IsPrimitiveRoot ζ 7) :
    charge (lambda hζ) = 7 := by
  rw [lambda_eq_neg_zeta_sub_one]
  rw [show -(hζ.toInteger - 1) =
      (-1 : 𝓞 K) * (hζ.toInteger - 1) by ring, charge_mul]
  have hneg : charge (-1 : 𝓞 K) = 1 := by
    simpa using charge_unit (K := K) (-1 : (𝓞 K)ˣ)
  rw [hneg, one_mul]
  simp only [charge]
  rw [hζ.norm_toInteger_sub_one_of_prime_ne_two' (by norm_num)]
  norm_num

omit [NumberField K] [IsCyclotomicExtension {7} ℚ K] in
/-- Charge is multiplicative on powers. -/
theorem charge_pow (z : 𝓞 K) (n : ℕ) :
    charge (z ^ n) = charge z ^ n := by
  simp only [charge, map_pow, Int.natAbs_pow]

/-- The charge visible after `n` ramified drain quanta. -/
def drainCharge (hζ : IsPrimitiveRoot ζ 7) (n : ℕ) : ℕ :=
  charge ((lambda hζ) ^ n)

/-- Powers of the ramified quantum expose the literal scale `7 ^ n`. -/
theorem drainCharge_eq (hζ : IsPrimitiveRoot ζ 7) (n : ℕ) :
    drainCharge hζ n = 7 ^ n := by
  rw [drainCharge, charge_pow, lambda_charge]

/-- The ramified charge scale is strictly increasing with its exponent; in
a descent, lowering that exponent is therefore a strict charge drain. -/
theorem drainCharge_strictMono (hζ : IsPrimitiveRoot ζ 7) :
    StrictMono (drainCharge hζ) := by
  intro m n hmn
  rw [drainCharge_eq, drainCharge_eq]
  exact Nat.pow_lt_pow_right (by norm_num) hmn

/-- One removal of a ramified factor strictly lowers the corresponding
charge. -/
theorem drainCharge_step (hζ : IsPrimitiveRoot ζ 7) (n : ℕ) :
    drainCharge hζ n < drainCharge hζ (n + 1) :=
  drainCharge_strictMono hζ (Nat.lt_succ_self n)

end CyclotomicSeven

end

end Fermat.Seven.Conservation
