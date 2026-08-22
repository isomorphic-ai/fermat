/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The exponent-59 conservation spine

This file is the literal structural composition boundary for the eighth
conservation rung.  It imports the proposition-only FLT statement and the
seven preceding conservation primitives, but no classical exponent-59 proof
and no generic irregular-prime machinery.

The credit column is not represented by an additive scalar here.  It is the
generated node-pair matrix in `Fermat.FiftyNine.Conservation.Credit`, whose
law is semilattice merge and whose opposite side is matrix transpose.

The conductor-specific portion specializes the generic N7 norm/gauge
primitive to a 59th cyclotomic field.  Its free unit rank is 28, and the
ramified quantum `1 - ζ₅₉` has charge 59.
-/
import Fermat.Core.Statement.Basic
import Fermat.Exponents.One.Conservation
import Fermat.Exponents.Two.PythagorasConservation
import Fermat.Exponents.Three.Conservation.Spine
import Fermat.Exponents.Four.Conservation.Descent
import Fermat.Exponents.Five.Conservation.Spine
import Fermat.Exponents.Six.Conservation.Spine
import Fermat.Exponents.Seven.Conservation.Spine
import Fermat.Experiments.Conservation.CyclotomicDrain
import Fermat.Exponents.FiftyNine.Conservation.Credit

open scoped BigOperators NumberField

namespace Fermat.FiftyNine.Conservation

/-! ## The seven stock laws at the composition boundary -/

/-- An audit receipt that every completed stock spine contributes its native
structural law.  This contains no exponent-59 solution state, credit
capacity, arithmetic repayment, or strict-successor constructor. -/
structure StockSpineReceipt : Prop where
  n1_vacuum : ∀ u v : ℕ, Fermat.One.coupling u v = 0
  n2_balance : ∀ {V : Type*} [NormedAddCommGroup V]
      [InnerProductSpace ℝ V] (u v : V),
    Fermat.Two.charge (u + v) =
      Fermat.Two.charge u + Fermat.Two.charge v +
        2 * Fermat.Two.coupling u v
  n3_drain : ∀ {m n : ℕ}, m < n →
    Fermat.Three.Conservation.drainCharge m <
      Fermat.Three.Conservation.drainCharge n
  n4_positive : ∀ S : Fermat.Four.Conservation.PrimitiveSolution,
    0 < S.stateCharge
  n5_gauge : ∀ (u : Fermat.Five.Conservation.GoldenIntˣ)
      (z : Fermat.Five.Conservation.GoldenInt),
    Fermat.Five.Conservation.goldenCharge ((u : _) * z) =
      Fermat.Five.Conservation.goldenCharge z
  n6_fold : ∀ a b : ℤ,
    a ^ 6 + b ^ 6 = (a ^ 2 + b ^ 2) *
      Fermat.Six.Conservation.charge
        (Fermat.Six.Conservation.cofactorElement a b)
  n7_lattice : ∀ {K : Type*} [Field K] [NumberField K]
      (u : (𝓞 K)ˣ),
    ∃! coordinates : Fermat.Seven.Conservation.FullGaugeCoordinates K,
      u = Fermat.Seven.Conservation.fullGaugeUnit K coordinates

/-- The seven stock laws are simultaneously available at the N59 boundary.
This is a receipt, not the missing transformer from an FLT solution to a
strictly smaller solution state. -/
theorem stockSpineReceipt : StockSpineReceipt where
  n1_vacuum := Fermat.One.coupling_empty
  n2_balance := Fermat.Two.charge_ledger
  n3_drain := Fermat.Three.Conservation.drainCharge_pred_lt
  n4_positive :=
    Fermat.Four.Conservation.PrimitiveSolution.stateCharge_pos
  n5_gauge := Fermat.Five.Conservation.charge_gauge_invariant
  n6_fold := Fermat.Six.Conservation.sixth_ledger
  n7_lattice := Fermat.Seven.Conservation.gauge_decomposition

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
  Fermat.Conservation.CyclotomicDrain.lambda hζ

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
/-- The requested orientation differs from `ζ₅₉ - 1` only by the unit
`-1`. -/
theorem lambda_eq_neg_zeta_sub_one (hζ : IsPrimitiveRoot ζ 59) :
    lambda hζ = -(hζ.toInteger - 1) := by
  exact
    Fermat.Conservation.CyclotomicDrain.lambda_eq_neg_zeta_sub_one hζ

/-- One ramified quantum has absolute norm charge exactly 59. -/
theorem lambda_charge (hζ : IsPrimitiveRoot ζ 59) :
    charge (lambda hζ) = 59 := by
  exact Fermat.Conservation.CyclotomicDrain.lambda_charge hζ

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
/-- Absolute norm charge is multiplicative on powers. -/
theorem charge_pow (z : 𝓞 K) (n : ℕ) :
    charge (z ^ n) = charge z ^ n :=
  Fermat.Conservation.CyclotomicDrain.charge_pow z n

/-- The charge stored in `n` ramified quanta. -/
def drainCharge (hζ : IsPrimitiveRoot ζ 59) (n : ℕ) : ℕ :=
  Fermat.Conservation.CyclotomicDrain.drainCharge hζ n

/-- `n` ramified quanta carry literal charge `59 ^ n`. -/
theorem drainCharge_eq (hζ : IsPrimitiveRoot ζ 59) (n : ℕ) :
    drainCharge hζ n = 59 ^ n := by
  exact Fermat.Conservation.CyclotomicDrain.drainCharge_eq hζ n

/-- Ramified charge is strictly increasing with multiplicity; lowering
multiplicity is therefore a strict drain. -/
theorem drainCharge_strictMono (hζ : IsPrimitiveRoot ζ 59) :
    StrictMono (drainCharge hζ) := by
  exact Fermat.Conservation.CyclotomicDrain.drainCharge_strictMono hζ

/-- Removing one ramified factor strictly lowers the associated charge. -/
theorem drainCharge_step (hζ : IsPrimitiveRoot ζ 59) (n : ℕ) :
    drainCharge hζ n < drainCharge hζ (n + 1) :=
  Fermat.Conservation.CyclotomicDrain.drainCharge_step hζ n

end CyclotomicFiftyNine

end

end Fermat.FiftyNine.Conservation
