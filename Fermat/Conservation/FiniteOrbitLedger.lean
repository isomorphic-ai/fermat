/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Finite-orbit Finsupp ledgers

This file seats a finite indexed family of additive values at named places.
An injective place map permits exact readback at every orbit index.  Values
away from the range vanish, the finite support is contained in that range,
and aggregating the ledger recovers the complete indexed sum.

The construction preserves the supplied index orientation literally: it
does not invert indices, insert character weights, identify the range with a
larger arithmetic support, or assert reciprocity.  Those interpretations
remain the responsibility of downstream adapters.
-/
import Mathlib.Data.Finsupp.Basic

open scoped BigOperators

noncomputable section

namespace Fermat.Conservation.FiniteOrbitLedger

universe uIndex uPlace uValue

variable {Index : Type uIndex} {Place : Type uPlace} {A : Type uValue}
  [Fintype Index] [AddCommMonoid A]

/-- Seat every indexed value at its corresponding place.  If distinct
indices name the same place, their values are added in that ledger row. -/
noncomputable def orbitLedger
    (place : Index → Place) (value : Index → A) : Place →₀ A :=
  ∑ index : Index, Finsupp.single (place index) (value index)

/-- An injectively indexed orbit reads back its original value at every
named place. -/
@[simp]
theorem orbitLedger_apply
    (place : Index → Place) (value : Index → A)
    (hinjective : Function.Injective place) (index : Index) :
    orbitLedger place value (place index) = value index := by
  classical
  change (∑ other : Index,
      Finsupp.single (place other) (value other)) (place index) = _
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single index]
  · simp
  · intro other _ hother
    rw [Finsupp.single_eq_of_ne]
    exact fun hplace ↦ hother (hinjective hplace.symm)
  · simp

/-- Every ledger row outside the range of the supplied place map is zero. -/
theorem orbitLedger_apply_eq_zero_of_not_mem_range
    (place : Index → Place) (value : Index → A)
    (v : Place) (hv : v ∉ Set.range place) :
    orbitLedger place value v = 0 := by
  classical
  change (∑ index : Index,
      Finsupp.single (place index) (value index)) v = 0
  rw [Finset.sum_apply']
  apply Finset.sum_eq_zero
  intro index _
  rw [Finsupp.single_eq_of_ne]
  exact fun hplace ↦ hv ⟨index, hplace.symm⟩

/-- The actual finite support is contained in the orbit range.  Equality is
not asserted because indexed values are allowed to vanish. -/
theorem orbitLedger_support_subset_range
    (place : Index → Place) (value : Index → A) :
    ↑(orbitLedger place value).support ⊆ Set.range place := by
  intro v hv
  by_contra hout
  exact (Finsupp.mem_support_iff.mp hv)
    (orbitLedger_apply_eq_zero_of_not_mem_range place value v hout)

/-- Aggregating the finite ledger recovers the complete indexed value sum,
even when the place map is not injective. -/
theorem orbitLedger_sum
    (place : Index → Place) (value : Index → A) :
    (orbitLedger place value).sum (fun _ entry ↦ entry) =
      ∑ index : Index, value index := by
  classical
  have hsum (s : Finset Index) :
      (∑ index ∈ s, Finsupp.single (place index) (value index)).sum
          (fun _ entry ↦ entry) =
        ∑ index ∈ s, value index := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert index s hindex ih =>
        rw [Finset.sum_insert hindex, Finset.sum_insert hindex,
          Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
          Finsupp.sum_single_index (by rfl), ih]
  change (∑ index : Index,
      Finsupp.single (place index) (value index)).sum
        (fun _ entry ↦ entry) = ∑ index : Index, value index
  simpa using hsum (Finset.univ : Finset Index)

end Fermat.Conservation.FiniteOrbitLedger
