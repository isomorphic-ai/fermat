/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Place-indexed Tate pairings and reciprocity ledgers

This file is an interface boundary.  Mathlib does not currently construct the
local Kummer--Artin/Tate pairings or prove their global reciprocity law.  The
two structures below state those arithmetic inputs with their exact laws.

The consequences are ordinary compiled conservation algebra.  Local readings
are retained as a `Finsupp`, so the type of all places need not be finite.  A
reciprocity witness becomes a literal `PlaceLedger`, then a three-column
`Ledger`, then a zero-spent `Transfer` to vacuum, and finally the scheduler's
L1 identity through `IsoConserveBridge`.
-/
import Fermat.Conservation.IsoConserveBridge
import Fermat.Conservation.LinkingInterfaces
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.ZMod.Basic

noncomputable section

namespace Fermat.Conservation.TatePairing

open Fermat.Conservation.LinkingInterfaces

universe uPlace uDelta uChi uDual uAlpha

/-! ## Reflected characters and the local adjoint interface -/

/-- The character paired with `chi` is definitionally its reflected
character `chi* = omega * chi⁻¹`; consequently `chi * chi* = omega`.

This is the character-level law behind the two carrier legs.  It does not
claim that an arithmetic local pairing has been constructed. -/
theorem character_mul_reflectedCharacter
    {O : Type*} {Delta : Type uDelta}
  [CommRing O] [CommGroup Delta]
  (omega chi : InvolutiveBase.Character O Delta) :
    chi * InvolutiveBase.reflectedCharacter omega chi = omega := by
  ext delta
  simp [InvolutiveBase.reflectedCharacter]

/-- Interface for the place-indexed local Tate pairing on the two reflected
Selmer legs.

The `Finsupp` codomain is the finite-support law: every pair of global
classes has only finitely many nonzero local readings.  The adjoint law is
the arithmetic realization of the existing Teichmuller-twisted `#`:

`pair_v (a • x) y = pair_v x (a# • y)`.

No value of this structure is supplied in the present repository. -/
structure PlaceIndexedLocalPairing
    (p : ℕ) [Fact p.Prime]
    (Delta : Type uDelta) [CommGroup Delta]
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta)
    (Place : Type uPlace) (SelmerChi : Type uChi)
    (DOmegaSelmerChiStar : Type uDual)
    [AddCommGroup SelmerChi]
    [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
    [AddCommGroup DOmegaSelmerChiStar]
    [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar] where
  readings :
    SelmerChi →+ (DOmegaSelmerChiStar →+ (Place →₀ ZMod p))
  adjoint_law : ∀ v a x y,
    readings (a • x) y v =
      readings x ((InvolutiveBase.hash omega a) • y) v

namespace PlaceIndexedLocalPairing

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt p) Delta}
  {Place : Type uPlace} {SelmerChi : Type uChi}
  {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar]

/-- One local column of the finite-support reading ledger. -/
def pairAt
    (pairing : PlaceIndexedLocalPairing p Delta omega chi Place
      SelmerChi DOmegaSelmerChiStar)
    (v : Place) (x : SelmerChi) (y : DOmegaSelmerChiStar) : ZMod p :=
  pairing.readings x y v

/-- Total of every retained local receipt away from one distinguished
place.  The `Finsupp` erasure keeps the definition finite even when the type
of all places is infinite. -/
def awayReadingTotal
    (pairing : PlaceIndexedLocalPairing p Delta omega chi Place
      SelmerChi DOmegaSelmerChiStar)
    (distinguished : Place) (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    ZMod p :=
  ((pairing.readings x y).erase distinguished).sum fun _ value ↦ value

/-- Total reading on a named finite collection of places. -/
def readingTotalOn
    (pairing : PlaceIndexedLocalPairing p Delta omega chi Place
      SelmerChi DOmegaSelmerChiStar)
    (places : Finset Place) (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    ZMod p :=
  ∑ v ∈ places, pairing.pairAt v x y

/-- Named projection of the arithmetic adjoint law. -/
theorem pairAt_smul_adjoint
    (pairing : PlaceIndexedLocalPairing p Delta omega chi Place
      SelmerChi DOmegaSelmerChiStar)
    (v : Place) (a : IntegralPadicGroupAlgebra p Delta)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    pairing.pairAt v (a • x) y =
      pairing.pairAt v x ((InvolutiveBase.hash omega a) • y) :=
  pairing.adjoint_law v a x y

/-- Moving an action across twice uses the proved involutivity of `#` and
returns the original action.  This theorem makes the link from the interface
law to `InvolutiveBase.hash_hash` proof-relevant and executable. -/
theorem pairAt_hash_smul_adjoint
    (pairing : PlaceIndexedLocalPairing p Delta omega chi Place
      SelmerChi DOmegaSelmerChiStar)
    (v : Place) (a : IntegralPadicGroupAlgebra p Delta)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    pairing.pairAt v ((InvolutiveBase.hash omega a) • x) y =
      pairing.pairAt v x (a • y) := by
  rw [pairing.pairAt_smul_adjoint]
  simp only [InvolutiveBase.hash_hash]

/-- The interface's `Finsupp` really gives finite support for the displayed
function of places. -/
theorem finite_support
    (pairing : PlaceIndexedLocalPairing p Delta omega chi Place
      SelmerChi DOmegaSelmerChiStar)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    Set.Finite (Function.support fun v => pairing.pairAt v x y) := by
  classical
  refine (pairing.readings x y).support.finite_toSet.subset ?_
  intro v hv
  exact Finsupp.mem_support_iff.mpr hv

end PlaceIndexedLocalPairing

/-! ## The retained place ledger and the existing conservation tunnel -/

/-- A finite place-indexed ledger before its entries are aggregated into the
repository's route-neutral three-column ledger. -/
structure PlaceLedger (Place : Type uPlace) (α : Type uAlpha)
    [AddCommMonoid α] where
  entries : Place →₀ α
  total : α
  conservation : entries.sum (fun _ value => value) = total

namespace PlaceLedger

variable {Place : Type uPlace} {α : Type uAlpha} [AddCommMonoid α]

/-- Aggregate all retained local columns into the stock column of the
existing literal ledger.  Credit and conversion remain empty. -/
def toLedger (ledger : PlaceLedger Place α) : Ledger α where
  stock := ledger.entries.sum fun _ value => value
  credit := 0
  converted := 0
  total := ledger.total
  conservation := by simpa using ledger.conservation

@[simp] theorem toLedger_stock (ledger : PlaceLedger Place α) :
    ledger.toLedger.stock = ledger.entries.sum (fun _ value => value) :=
  rfl

@[simp] theorem toLedger_credit (ledger : PlaceLedger Place α) :
    ledger.toLedger.credit = 0 :=
  rfl

@[simp] theorem toLedger_converted (ledger : PlaceLedger Place α) :
    ledger.toLedger.converted = 0 :=
  rfl

@[simp] theorem toLedger_total (ledger : PlaceLedger Place α) :
    ledger.toLedger.total = ledger.total :=
  rfl

/-- A zero-total place ledger is an actual zero-spent transaction to the
literal vacuum.  Its available-column equation uses the carried place sum,
so reciprocity is not replaced by a reflexive transfer. -/
def toVacuumTransfer (ledger : PlaceLedger Place α)
    (htotal : ledger.total = 0) : Transfer α where
  before := ledger.toLedger
  after := Ledger.vacuum
  spent := 0
  before_conserved := Ledger.conservation_identity ledger.toLedger
  after_conserved := Ledger.conservation_identity Ledger.vacuum
  total_preserved := by
    change ledger.total = 0
    exact htotal
  available_decomposition := by
    change ledger.entries.sum (fun _ value => value) + 0 = 0 + 0 + 0
    rw [ledger.conservation, htotal]
    simp
  converted_decomposition := by simp [toLedger, Ledger.vacuum]

@[simp] theorem toVacuumTransfer_before
    (ledger : PlaceLedger Place α) (htotal : ledger.total = 0) :
    (ledger.toVacuumTransfer htotal).before = ledger.toLedger :=
  rfl

@[simp] theorem toVacuumTransfer_after
    (ledger : PlaceLedger Place α) (htotal : ledger.total = 0) :
    (ledger.toVacuumTransfer htotal).after = Ledger.vacuum :=
  rfl

@[simp] theorem toVacuumTransfer_spent
    (ledger : PlaceLedger Place α) (htotal : ledger.total = 0) :
    (ledger.toVacuumTransfer htotal).spent = 0 :=
  rfl

/-- The place ledger enters the existing scheduler tunnel as its exact L1
conservation identity. -/
theorem toVacuumTransfer_L1
    (ledger : PlaceLedger Place α) (htotal : ledger.total = 0) :
    IsoConserveStatements.Columns.accounted
        (IsoConserveBridge.toColumns
          (ledger.toVacuumTransfer htotal).after) =
      IsoConserveStatements.Columns.accounted
        (IsoConserveBridge.toColumns
          (ledger.toVacuumTransfer htotal).before) :=
  IsoConserveBridge.transfer_L1_conservation
    (ledger.toVacuumTransfer htotal)

end PlaceLedger

/-! ## Global reciprocity as conservation -/

/-- Interface for global reciprocity on one place-indexed local pairing.
The local `Finsupp` is already the finite-support witness; this law says the
sum of all its columns is zero for every pair of global classes. -/
structure GlobalReciprocityLaw
    {p : ℕ} [Fact p.Prime]
    {Delta : Type uDelta} [CommGroup Delta]
    {omega chi : InvolutiveBase.Character (PadicInt p) Delta}
    {Place : Type uPlace} {SelmerChi : Type uChi}
    {DOmegaSelmerChiStar : Type uDual}
    [AddCommGroup SelmerChi]
    [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
    [AddCommGroup DOmegaSelmerChiStar]
    [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar]
    (pairing : PlaceIndexedLocalPairing p Delta omega chi Place
      SelmerChi DOmegaSelmerChiStar) : Prop where
  sum_eq_zero : ∀ x y,
    (pairing.readings x y).sum (fun _ value => value) = 0

namespace GlobalReciprocityLaw

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt p) Delta}
  {Place : Type uPlace} {SelmerChi : Type uChi}
  {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar]
  {pairing : PlaceIndexedLocalPairing p Delta omega chi Place
    SelmerChi DOmegaSelmerChiStar}

/-- The place-indexed reciprocity ledger for two global classes. -/
def placeLedger (reciprocity : GlobalReciprocityLaw pairing)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    PlaceLedger Place (ZMod p) where
  entries := pairing.readings x y
  total := 0
  conservation := reciprocity.sum_eq_zero x y

/-- Global reciprocity as the named conservation identity of the aggregated
three-column ledger. -/
theorem ledger_conservation_identity
    (reciprocity : GlobalReciprocityLaw pairing)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    (reciprocity.placeLedger x y).toLedger.stock +
        (reciprocity.placeLedger x y).toLedger.credit +
        (reciprocity.placeLedger x y).toLedger.converted =
      (reciprocity.placeLedger x y).toLedger.total :=
  Ledger.conservation_identity (reciprocity.placeLedger x y).toLedger

/-- Reciprocity as a literal zero-spent transfer from the local-reading
ledger to vacuum. -/
def reciprocityTransfer (reciprocity : GlobalReciprocityLaw pairing)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) : Transfer (ZMod p) :=
  (reciprocity.placeLedger x y).toVacuumTransfer rfl

/-- The prime-place ledger's compiled scheduler L1 law. -/
theorem reciprocity_L1_conservation
    (reciprocity : GlobalReciprocityLaw pairing)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    IsoConserveStatements.Columns.accounted
        (IsoConserveBridge.toColumns
          (reciprocity.reciprocityTransfer x y).after) =
      IsoConserveStatements.Columns.accounted
        (IsoConserveBridge.toColumns
          (reciprocity.reciprocityTransfer x y).before) :=
  IsoConserveBridge.transfer_L1_conservation
    (reciprocity.reciprocityTransfer x y)

/-- Reciprocity reads one distinguished column as the negative total of
every other retained column, without collapsing the away support. -/
theorem pairAt_eq_neg_awayReadingTotal
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place) (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    pairing.pairAt distinguished x y =
      -pairing.awayReadingTotal distinguished x y := by
  classical
  have hsum := reciprocity.sum_eq_zero x y
  rw [← Finsupp.erase_add_single distinguished (pairing.readings x y),
    Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)] at hsum
  have hbalanced :
      pairing.awayReadingTotal distinguished x y +
          pairing.pairAt distinguished x y = 0 := by
    simpa [PlaceIndexedLocalPairing.awayReadingTotal,
      PlaceIndexedLocalPairing.pairAt] using hsum
  exact eq_neg_of_add_eq_zero_right hbalanced

/-- If all columns outside one distinguished place and a finite retained set
are silent, reciprocity balances the distinguished column against the exact
total on that set. -/
theorem pairAt_eq_neg_readingTotalOn
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place) (places : Finset Place)
    (hdistinguished : distinguished ∉ places)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (houtside : ∀ v, v ≠ distinguished → v ∉ places →
      pairing.pairAt v x y = 0) :
    pairing.pairAt distinguished x y =
      -pairing.readingTotalOn places x y := by
  classical
  let entries := pairing.readings x y
  have hsupport : entries.support ⊆ insert distinguished places := by
    intro v hv
    rw [Finset.mem_insert]
    by_cases hvd : v = distinguished
    · exact Or.inl hvd
    · refine Or.inr ?_
      by_contra hvp
      exact (Finsupp.mem_support_iff.mp hv) (houtside v hvd hvp)
  have hsum_support :
      entries.support.sum (fun v ↦ entries v) = 0 :=
    reciprocity.sum_eq_zero x y
  have hsum_insert :
      (insert distinguished places).sum (fun v ↦ entries v) = 0 := by
    calc
      (insert distinguished places).sum (fun v ↦ entries v) =
          entries.support.sum (fun v ↦ entries v) := by
        symm
        apply Finset.sum_subset hsupport
        intro v _hv hnot
        by_contra hne
        exact hnot (Finsupp.mem_support_iff.mpr hne)
      _ = 0 := hsum_support
  have hbalanced :
      pairing.pairAt distinguished x y +
          pairing.readingTotalOn places x y = 0 := by
    rw [Finset.sum_insert hdistinguished] at hsum_insert
    simpa [PlaceIndexedLocalPairing.readingTotalOn,
      PlaceIndexedLocalPairing.pairAt, entries] using hsum_insert
  exact eq_neg_of_add_eq_zero_left hbalanced

/-- If every local column except one is silent, reciprocity silences the
remaining column. -/
theorem pairAt_eq_zero_of_other_places
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished : Place) (x : SelmerChi)
    (y : DOmegaSelmerChiStar)
    (hother : ∀ v, v ≠ distinguished → pairing.pairAt v x y = 0) :
    pairing.pairAt distinguished x y = 0 := by
  classical
  have hentries :
      pairing.readings x y =
        Finsupp.single distinguished
          (pairing.pairAt distinguished x y) := by
    ext v
    by_cases hv : v = distinguished
    · subst v
      simp [PlaceIndexedLocalPairing.pairAt]
    · rw [Finsupp.single_eq_of_ne hv]
      exact hother v hv
  have hsum := reciprocity.sum_eq_zero x y
  rw [hentries] at hsum
  simpa using hsum

/-- If every local column outside two distinct retained places is silent,
global reciprocity retains their exact two-term balance.  Unlike the
one-column corollary above, this theorem does not erase the auxiliary
receipt. -/
theorem pairAt_add_pairAt_eq_zero_of_outside_two
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished auxiliary : Place)
    (hne : distinguished ≠ auxiliary)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (hother : ∀ v, v ≠ distinguished → v ≠ auxiliary →
      pairing.pairAt v x y = 0) :
    pairing.pairAt distinguished x y +
        pairing.pairAt auxiliary x y = 0 := by
  classical
  have hentries :
      pairing.readings x y =
        Finsupp.single distinguished
            (pairing.pairAt distinguished x y) +
          Finsupp.single auxiliary (pairing.pairAt auxiliary x y) := by
    ext v
    change pairing.pairAt v x y = _
    by_cases hvd : v = distinguished
    · subst v
      simp [hne, PlaceIndexedLocalPairing.pairAt]
    · by_cases hva : v = auxiliary
      · subst v
        simp [hne, PlaceIndexedLocalPairing.pairAt]
      · calc
          pairing.pairAt v x y = 0 := hother v hvd hva
          _ = (Finsupp.single distinguished
                  (pairing.pairAt distinguished x y) +
                Finsupp.single auxiliary
                  (pairing.pairAt auxiliary x y)) v := by
            simp [hvd, hva]
  have hsum := reciprocity.sum_eq_zero x y
  rw [hentries,
    Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hsum
  simpa using hsum

/-- Oriented form of the two-place conservation law: the wild reading is
the negative of the retained auxiliary reading. -/
theorem pairAt_eq_neg_pairAt_of_outside_two
    (reciprocity : GlobalReciprocityLaw pairing)
    (distinguished auxiliary : Place)
    (hne : distinguished ≠ auxiliary)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (hother : ∀ v, v ≠ distinguished → v ≠ auxiliary →
      pairing.pairAt v x y = 0) :
    pairing.pairAt distinguished x y =
      -pairing.pairAt auxiliary x y :=
  eq_neg_of_add_eq_zero_left
    (reciprocity.pairAt_add_pairAt_eq_zero_of_outside_two
      distinguished auxiliary hne x y hother)

end GlobalReciprocityLaw

/-! ## Explicit local-condition orthogonality -/

/-- The guard required before a local reading may be declared silent.
Membership in a global Selmer group alone is deliberately absent: the
localized primal condition and localized dual condition must be named and
proved orthogonal at this particular place. -/
structure LocalOrthogonalityGuard
    {p : ℕ} [Fact p.Prime]
    {Delta : Type uDelta} [CommGroup Delta]
    {omega chi : InvolutiveBase.Character (PadicInt p) Delta}
    {Place : Type uPlace} {SelmerChi : Type uChi}
    {DOmegaSelmerChiStar : Type uDual}
    [AddCommGroup SelmerChi]
    [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
    [AddCommGroup DOmegaSelmerChiStar]
    [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar]
    (pairing : PlaceIndexedLocalPairing p Delta omega chi Place
      SelmerChi DOmegaSelmerChiStar)
    (v : Place) (x : SelmerChi) (y : DOmegaSelmerChiStar) where
  primalCondition : AddSubgroup SelmerChi
  dualCondition : AddSubgroup DOmegaSelmerChiStar
  primal_mem : x ∈ primalCondition
  dual_mem : y ∈ dualCondition
  orthogonal : ∀ x' ∈ primalCondition, ∀ y' ∈ dualCondition,
    pairing.pairAt v x' y' = 0

namespace LocalOrthogonalityGuard

variable {p : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt p) Delta}
  {Place : Type uPlace} {SelmerChi : Type uChi}
  {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra p Delta) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra p Delta) DOmegaSelmerChiStar]
  {pairing : PlaceIndexedLocalPairing p Delta omega chi Place
    SelmerChi DOmegaSelmerChiStar}
  {v : Place} {x : SelmerChi} {y : DOmegaSelmerChiStar}

/-- A local reading vanishes only after the two local-condition membership
proofs and their orthogonality law have all been consumed. -/
theorem pairAt_eq_zero
    (guard : LocalOrthogonalityGuard pairing v x y) :
    pairing.pairAt v x y = 0 :=
  guard.orthogonal x guard.primal_mem y guard.dual_mem

end LocalOrthogonalityGuard

end Fermat.Conservation.TatePairing
