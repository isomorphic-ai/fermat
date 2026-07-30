/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The selected gauge-quotient permits

This file is the conductor-specific W1 instance layer.  It packages the
already checked capacity, repayment, and exact depth-two certificates into
the generic quotient record.  No numerical datum is copied into the generic
core.
-/
import Fermat.Conservation.Credit.GaugeQuotient
import Fermat.FiftyNine.Conservation.DepthCertificate
import Fermat.FiftyNine.Conservation.Spine

open scoped NumberField

namespace Fermat.FiftyNine.Conservation.GaugeQuotient

open Fermat.Conservation.Credit

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {ζ : K}

/-- The three checked conductor-59 permits, assembled at their common
real-unit carrier. -/
def primeData (hζ : IsPrimitiveRoot ζ 59) :
    Fermat.Conservation.Credit.GaugeQuotient.PrimeData
      59 Credit.exponentCycle (Credit.realOrbitNode hζ)
      (Instance.IsDeeplyRepayable hζ) Instance.realGaugeData where
  prime := by norm_num
  capacity := Instance.capacityData hζ
  capacity_ambient := rfl
  faithfulAtPrime := by
    rw [Fermat.Conservation.Credit.GaugeQuotient.FaithfulAt,
      ← Subgroup.index_eq_card]
    change (Credit.generatedSubledger hζ).index.Coprime 59
    rw [← Credit.capacityIndex_eq_relIndex hζ]
    exact
      ((by norm_num : Nat.Prime 59).coprime_iff_not_dvd.mpr
        (CapacityCertificate.capacityCertificate hζ).2).symm
  repayment_of_capacity_and_flow := by
    intro u hdeep
    exact Instance.repayment_of_capacity_and_flow hζ hdeep
  depthTwo := DepthCertificate.depthTwoCertificate

/-- Every element of the generated real-unit gauge preserves the stock
absolute-norm charge. -/
theorem generatedGauge_chargeInvariant
    (hζ : IsPrimitiveRoot ζ 59) :
    Fermat.Conservation.Credit.GaugeQuotient.ChargeInvariant
      (primeData hζ).generatedGauge
      (Fermat.Seven.Conservation.charge (K := K)) := by
  intro g state
  change
    Fermat.Seven.Conservation.charge
        (((g.1.1 : (𝓞 K)ˣ) : 𝓞 K) * state) =
      Fermat.Seven.Conservation.charge state
  exact
    Fermat.Seven.Conservation.charge_unit_invariant
      (g.1.1 : (𝓞 K)ˣ) state

/-- The stock norm is actually invariant under every generated real unit,
so the exact depth-two permit is more than sufficient for the generic
Jacobian bridge. -/
def stockDepthTwoJacobianBridge
    (hζ : IsPrimitiveRoot ζ 59) :
    (primeData hζ).DepthTwoJacobianBridge
      (Fermat.Seven.Conservation.charge (K := K)) :=
  fun _depthTwo => generatedGauge_chargeInvariant hζ

/-- Applying the generic quotient morphism to the actual generated debit
ledger leaves the vacuum ledger. -/
theorem debitLedger_quotient_eq_bot
    (hζ : IsPrimitiveRoot ζ 59) :
    (primeData hζ).quotientLedgerMorphism
        (Credit.debitLedger hζ) =
      ⊥ := by
  rw [Credit.debitLedger, Credit.fundedGenerators_eq_univ]
  change
    (primeData hζ).quotientLedgerMorphism
        ((primeData hζ).sourceLedger) =
      ⊥
  rw [← (primeData hζ).quotientLedger_eq_morphism]
  exact (primeData hζ).quotientLedger_eq_bot

/-- The selected quotient has vacuum residual credit and preserves the
absolute-norm charge of every integral stock state. -/
theorem quotient_vacuum_and_charge_eq
    (hζ : IsPrimitiveRoot ζ 59) (state : 𝓞 K) :
    (primeData hζ).quotientLedgerMorphism
        (Credit.debitLedger hζ) =
        ⊥ ∧
      (primeData hζ).quotientCharge
          (Fermat.Seven.Conservation.charge (K := K))
          (stockDepthTwoJacobianBridge hζ
            (primeData hζ).depthTwo)
          ((primeData hζ).quotientState state) =
        Fermat.Seven.Conservation.charge state :=
  ⟨debitLedger_quotient_eq_bot hζ,
    (primeData hζ).quotientCharge_quotientState
      (Fermat.Seven.Conservation.charge (K := K))
      (stockDepthTwoJacobianBridge hζ
        (primeData hζ).depthTwo)
      state⟩

end

end Fermat.FiftyNine.Conservation.GaugeQuotient
