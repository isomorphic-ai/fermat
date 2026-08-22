/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Pointed finite-orbit Finsupp ledgers

This file adjoins one distinguished row to a finite-orbit ledger.  The
construction is deliberately scalar and route-neutral: it records one named
value together with an indexed orbit, but does not interpret either row as a
local pairing, insert character weights, or assert reciprocity.

When the distinguished place is disjoint from the orbit range, both parts can
be read back exactly.  Away from their union the ledger vanishes, its support
is contained in that union, and its total is the distinguished value plus the
complete indexed sum.
-/
import Fermat.Experiments.Conservation.FiniteOrbitLedger

open scoped BigOperators

noncomputable section

namespace Fermat.Conservation.PointedFiniteOrbitLedger

universe uIndex uPlace uValue

variable {Index : Type uIndex} {Place : Type uPlace} {A : Type uValue}
  [Fintype Index] [AddCommMonoid A]

/-- Adjoin one distinguished row to a finite indexed orbit ledger. -/
noncomputable def pointedOrbitLedger
    (distinguished : Place) (distinguishedValue : A)
    (place : Index → Place) (value : Index → A) : Place →₀ A :=
  Finsupp.single distinguished distinguishedValue +
    FiniteOrbitLedger.orbitLedger place value

/-- The distinguished row reads back exactly when it lies outside the orbit. -/
@[simp]
theorem pointedOrbitLedger_apply_distinguished
    (distinguished : Place) (distinguishedValue : A)
    (place : Index → Place) (value : Index → A)
    (hdisjoint : distinguished ∉ Set.range place) :
    pointedOrbitLedger distinguished distinguishedValue place value distinguished =
      distinguishedValue := by
  classical
  simp [pointedOrbitLedger,
    FiniteOrbitLedger.orbitLedger_apply_eq_zero_of_not_mem_range,
    hdisjoint]

/-- Every injectively indexed orbit row reads back exactly when the
distinguished place lies outside the orbit. -/
@[simp]
theorem pointedOrbitLedger_apply_orbit
    (distinguished : Place) (distinguishedValue : A)
    (place : Index → Place) (value : Index → A)
    (hinjective : Function.Injective place)
    (hdisjoint : distinguished ∉ Set.range place)
    (index : Index) :
    pointedOrbitLedger distinguished distinguishedValue place value (place index) =
      value index := by
  classical
  have hne : distinguished ≠ place index := by
    intro heq
    exact hdisjoint ⟨index, heq.symm⟩
  simp [pointedOrbitLedger, hne,
    FiniteOrbitLedger.orbitLedger_apply, hinjective]

/-- Every row outside the distinguished place and the orbit range is zero. -/
theorem pointedOrbitLedger_apply_eq_zero_of_ne_of_not_mem_range
    (distinguished : Place) (distinguishedValue : A)
    (place : Index → Place) (value : Index → A)
    (v : Place) (hne : v ≠ distinguished) (hout : v ∉ Set.range place) :
    pointedOrbitLedger distinguished distinguishedValue place value v = 0 := by
  classical
  simp [pointedOrbitLedger, Finsupp.single_eq_of_ne hne,
    FiniteOrbitLedger.orbitLedger_apply_eq_zero_of_not_mem_range,
    hout]

/-- The finite support is contained in the distinguished row together with
the orbit range.  Equality is not asserted because values may vanish. -/
theorem pointedOrbitLedger_support_subset_insert_range
    (distinguished : Place) (distinguishedValue : A)
    (place : Index → Place) (value : Index → A) :
    ↑(pointedOrbitLedger distinguished distinguishedValue place value).support ⊆
      Set.insert distinguished (Set.range place) := by
  intro v hv
  by_contra hout
  have hne : v ≠ distinguished := fun heq ↦
    hout (Set.mem_insert_iff.mpr (Or.inl heq))
  have horbit : v ∉ Set.range place := fun hmem ↦
    hout (Set.mem_insert_of_mem distinguished hmem)
  exact (Finsupp.mem_support_iff.mp hv)
    (pointedOrbitLedger_apply_eq_zero_of_ne_of_not_mem_range
      distinguished distinguishedValue place value v hne horbit)

/-- Aggregating the pointed ledger recovers its distinguished value plus the
complete indexed orbit sum. -/
theorem pointedOrbitLedger_sum
    (distinguished : Place) (distinguishedValue : A)
    (place : Index → Place) (value : Index → A) :
    (pointedOrbitLedger distinguished distinguishedValue place value).sum
        (fun _ entry ↦ entry) =
      distinguishedValue + ∑ index : Index, value index := by
  classical
  rw [pointedOrbitLedger,
    Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
    Finsupp.sum_single_index (by rfl),
    FiniteOrbitLedger.orbitLedger_sum]

end Fermat.Conservation.PointedFiniteOrbitLedger
