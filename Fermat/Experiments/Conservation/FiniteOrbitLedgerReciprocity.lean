/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Finite-orbit ledgers under global reciprocity

This file connects the route-neutral `FiniteOrbitLedger` construction to an
honest place-indexed global reciprocity law.  A distinguished reading and a
complete injectively indexed finite orbit reconstruct the full `Finsupp` of
local readings.  Global reciprocity then yields the exact scalar balance,
and zero or nonzero ledger totals give the corresponding distinguished
consequences.

Every arithmetic input remains visible.  The module does not construct a
local pairing or a reciprocity witness, identify an abstract index with an
arithmetic support, prove that a distinguished place is disjoint from that
support, compare any local value, or silence any omitted place.  It assumes
those receipts explicitly and performs only finite-ledger and conservation
algebra.  In particular, it has no cyclotomic, regularity, character-mode,
or cardinality hypothesis on the orbit.
-/
import Fermat.Experiments.Conservation.FiniteOrbitLedger
import Fermat.Experiments.Conservation.TatePairing

noncomputable section

namespace Fermat.Conservation.FiniteOrbitLedgerReciprocity

open Fermat.Conservation.FiniteOrbitLedger
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.TatePairing

universe uIndex uPlace uDelta uChi uDual uValue

/-! ## Route-neutral ledger consequences -/

variable {Index : Type uIndex} {Place : Type uPlace} {A : Type uValue}
  [Fintype Index] [AddCommMonoid A]

/-- A finite-support ledger with nonzero aggregate is itself nonzero. -/
theorem ledger_ne_zero_of_sum_ne_zero
    (ledger : Place →₀ A)
    (hsum : ledger.sum (fun _ entry ↦ entry) ≠ 0) :
    ledger ≠ 0 := by
  intro hledger
  apply hsum
  rw [hledger]
  simp

/-- If a distinguished value balances a nonzero ledger total, then the
distinguished value is nonzero. -/
theorem distinguished_ne_zero_of_add_ledger_sum_eq_zero
    (ledger : Place →₀ A) (distinguishedValue : A)
    (hsum : ledger.sum (fun _ entry ↦ entry) ≠ 0)
    (hbalance : distinguishedValue +
      ledger.sum (fun _ entry ↦ entry) = 0) :
    distinguishedValue ≠ 0 := by
  intro hdistinguished
  rw [hdistinguished, zero_add] at hbalance
  exact hsum hbalance

/-- If a distinguished value balances a zero ledger total, then the
distinguished value vanishes. -/
theorem distinguished_eq_zero_of_add_ledger_sum_eq_zero
    (ledger : Place →₀ A) (distinguishedValue : A)
    (hsum : ledger.sum (fun _ entry ↦ entry) = 0)
    (hbalance : distinguishedValue +
      ledger.sum (fun _ entry ↦ entry) = 0) :
    distinguishedValue = 0 := by
  rw [hsum, add_zero] at hbalance
  exact hbalance

/-- On an injectively seated orbit, one nonzero indexed value certifies that
the complete orbit ledger is nonzero. -/
theorem orbitLedger_ne_zero_of_value_ne_zero
    (place : Index → Place) (value : Index → A)
    (hinjective : Function.Injective place) (index : Index)
    (hvalue : value index ≠ 0) :
    orbitLedger place value ≠ 0 := by
  intro hledger
  apply hvalue
  rw [← orbitLedger_apply place value hinjective index, hledger]
  exact Finsupp.zero_apply

/-! ## Reconstruction of the full place-indexed readings -/

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt p) Delta}
  {SelmerChi : Type uChi} {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar]
  {pairing : PlaceIndexedLocalPairing p Delta omega chi Place
    SelmerChi DOmegaSelmerChiStar}

/-- Pointwise comparison on one distinguished place and a complete finite
orbit reconstructs the pairing's literal finite-support reading ledger.

The orbit comparison, injectivity, disjointness, and silence outside the
displayed range are all explicit.  Thus this theorem cannot invent a local
value or hide an incomplete support behind the `Finsupp` representation. -/
theorem readings_eq_single_add_orbitLedger
    (distinguished : Place) (place : Index → Place)
    (hinjective : Function.Injective place)
    (hdisjoint : ∀ index, place index ≠ distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (distinguishedValue : ZMod p)
    (hdistinguished :
      pairing.pairAt distinguished x y = distinguishedValue)
    (value : Index → ZMod p)
    (horbit : ∀ index,
      pairing.pairAt (place index) x y = value index)
    (houtside : ∀ v, v ≠ distinguished →
      v ∉ Set.range place → pairing.pairAt v x y = 0) :
    pairing.readings x y =
      Finsupp.single distinguished distinguishedValue +
        orbitLedger place value := by
  classical
  ext v
  change pairing.pairAt v x y = _
  by_cases hvd : v = distinguished
  · subst v
    rw [hdistinguished, Finsupp.add_apply, Finsupp.single_eq_same,
      orbitLedger_apply_eq_zero_of_not_mem_range, add_zero]
    rintro ⟨index, hindex⟩
    exact hdisjoint index hindex
  · by_cases hvOrbit : v ∈ Set.range place
    · obtain ⟨index, rfl⟩ := hvOrbit
      rw [horbit, Finsupp.add_apply, Finsupp.single_eq_of_ne, zero_add,
        orbitLedger_apply place value hinjective index]
      exact hdisjoint index
    · rw [houtside v hvd hvOrbit, Finsupp.add_apply,
        Finsupp.single_eq_of_ne,
        orbitLedger_apply_eq_zero_of_not_mem_range place value v hvOrbit,
        zero_add]
      exact hvd

/-! ## Global reciprocity consequences -/

/-- An honest global reciprocity law turns the reconstructed reading ledger
into the exact balance between its distinguished value and complete orbit
total.  Reciprocity remains a supplied witness. -/
theorem wild_add_orbitLedger_sum_eq_zero_of_globalReciprocity
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place) (place : Index → Place)
    (hinjective : Function.Injective place)
    (hdisjoint : ∀ index, place index ≠ distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (distinguishedValue : ZMod p)
    (hdistinguished :
      pairing.pairAt distinguished x y = distinguishedValue)
    (value : Index → ZMod p)
    (horbit : ∀ index,
      pairing.pairAt (place index) x y = value index)
    (houtside : ∀ v, v ≠ distinguished →
      v ∉ Set.range place → pairing.pairAt v x y = 0) :
    distinguishedValue + (orbitLedger place value).sum
        (fun _ entry ↦ entry) = 0 := by
  have hreadings := readings_eq_single_add_orbitLedger
    (pairing := pairing) distinguished place hinjective hdisjoint x y
      distinguishedValue hdistinguished value horbit houtside
  calc
    distinguishedValue +
        (orbitLedger place value).sum (fun _ entry ↦ entry) =
      (Finsupp.single distinguished distinguishedValue +
        orbitLedger place value).sum (fun _ entry ↦ entry) := by
          rw [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
            Finsupp.sum_single_index (by rfl)]
    _ = (pairing.readings x y).sum (fun _ entry ↦ entry) := by
      rw [hreadings]
    _ = 0 := reciprocity.sum_eq_zero x y

/-- If the displayed complete orbit ledger has zero total, genuine global
reciprocity forces the distinguished local reading to vanish. -/
theorem pairAt_eq_zero_of_globalReciprocity_of_orbitLedger_sum_eq_zero
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place) (place : Index → Place)
    (hinjective : Function.Injective place)
    (hdisjoint : ∀ index, place index ≠ distinguished)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (value : Index → ZMod p)
    (horbit : ∀ index,
      pairing.pairAt (place index) x y = value index)
    (houtside : ∀ v, v ≠ distinguished →
      v ∉ Set.range place → pairing.pairAt v x y = 0)
    (hsum : (orbitLedger place value).sum
      (fun _ entry ↦ entry) = 0) :
    pairing.pairAt distinguished x y = 0 := by
  have hbalance :=
    wild_add_orbitLedger_sum_eq_zero_of_globalReciprocity
      (pairing := pairing) reciprocity distinguished place hinjective
        hdisjoint x y (pairing.pairAt distinguished x y) rfl value
        horbit houtside
  rw [hsum, add_zero] at hbalance
  exact hbalance

end Fermat.Conservation.FiniteOrbitLedgerReciprocity
