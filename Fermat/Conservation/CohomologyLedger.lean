/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Cohomology is the credit column

The primary object in this file is the canonical filtration

`0 ≤ B ≤ Z ≤ C`.

Its two associated short exact sequences retain the extension data; no
section, retraction, complement, or product decomposition is selected.  An
additive invariant first sees the resulting K0 ledger, and a numerical
observer sees only its still lossier three-column shadow.  Thus the hierarchy
is: exact filtration, then K0 ledger, then numeric ledger.
-/
import Fermat.Conservation.IsoConserveBridge
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Length

noncomputable section

namespace Fermat.Conservation

universe uK uV uA

/-- A cochain cell with consecutive differentials whose composite is zero.

Finite-dimensionality is deliberately not stored as data: the filtration and
its exact sequences exist for every cell, while finrank observers request the
usual typeclass only where they are evaluated. -/
structure CohomologyExactCell
    (K : Type uK) [DivisionRing K]
    (Vprev V Vnext : Type uV)
    [AddCommGroup Vprev] [Module K Vprev]
    [AddCommGroup V] [Module K V]
    [AddCommGroup Vnext] [Module K Vnext] where
  dPrev : Vprev →ₗ[K] V
  dNext : V →ₗ[K] Vnext
  d_squared : dNext.comp dPrev = 0

namespace CohomologyExactCell

variable {K : Type uK} [DivisionRing K]
  {Vprev V Vnext : Type uV}
  [AddCommGroup Vprev] [Module K Vprev]
  [AddCommGroup V] [Module K V]
  [AddCommGroup Vnext] [Module K Vnext]

/-! ## W1: the executable cell -/

/-- Inherited flow: boundaries arriving from the previous cell. -/
def B (cell : CohomologyExactCell K Vprev V Vnext) : Submodule K V :=
  LinearMap.range cell.dPrev

/-- Unresolved potential: cocycles retained by the next differential. -/
def Z (cell : CohomologyExactCell K Vprev V Vnext) : Submodule K V :=
  LinearMap.ker cell.dNext

/-- The square-zero law places every boundary inside the cycle space. -/
theorem B_le_Z (cell : CohomologyExactCell K Vprev V Vnext) :
    cell.B ≤ cell.Z :=
  LinearMap.range_le_ker_iff.mpr cell.d_squared

/-- The boundary subspace as a submodule of the cycle subtype.

This is the unavoidable typed form of `B` in the quotient `Z / B`: ambient
`B : Submodule K V` cannot itself be used as a submodule of the type `Z`. -/
def BInZ (cell : CohomologyExactCell K Vprev V Vnext) :
    Submodule K cell.Z :=
  cell.B.comap cell.Z.subtype

/-- Cohomology, the unresolved potential modulo inherited flow. -/
abbrev H (cell : CohomologyExactCell K Vprev V Vnext) :=
  cell.Z ⧸ cell.BInZ

/-- Outgoing action: the range transferred into the next cell. -/
def Bout (cell : CohomologyExactCell K Vprev V Vnext) :
    Submodule K Vnext :=
  LinearMap.range cell.dNext

/-- The canonical filtration, stated in the ambient submodule lattice. -/
theorem canonical_filtration
    (cell : CohomologyExactCell K Vprev V Vnext) :
    (⊥ : Submodule K V) ≤ cell.B ∧ cell.B ≤ cell.Z ∧ cell.Z ≤ ⊤ :=
  ⟨bot_le, cell.B_le_Z, le_top⟩

/-- Exact input forms are cycles: the executable square-zero equation. -/
theorem exact_is_cycle
    (cell : CohomologyExactCell K Vprev V Vnext) (x : Vprev) :
    cell.dNext (cell.dPrev x) = 0 := by
  have h := LinearMap.congr_fun cell.d_squared x
  simpa using h

/-- A dual cycle is a functional whose pullback along `dPrev` is zero.

Writing the condition as a composite keeps the construction valid over a
possibly noncommutative division ring; no scalar action on the dual space is
needed. -/
def IsDualCycle
    (cell : CohomologyExactCell K Vprev V Vnext)
    (cycle : Module.Dual K V) : Prop :=
  cycle.comp cell.dPrev = 0

/-- Exact forms have zero period on dual cycles: evaluating a dual cycle on
any inherited boundary produces no private gain. -/
theorem exact_form_vanishes_on_dual_cycle
    (cell : CohomologyExactCell K Vprev V Vnext)
    (cycle : Module.Dual K V) (hcycle : cell.IsDualCycle cycle)
    (x : Vprev) : cycle (cell.dPrev x) = 0 := by
  change cycle.comp cell.dPrev = 0 at hcycle
  have h := LinearMap.congr_fun hcycle x
  simpa using h

/-- A short exact sequence of linear maps, with no selected splitting data. -/
structure LinearShortExactSequence
    (R : Type uK) [Ring R]
    (Left Middle Right : Type uV)
    [AddCommGroup Left] [Module R Left]
    [AddCommGroup Middle] [Module R Middle]
    [AddCommGroup Right] [Module R Right] where
  inclusion : Left →ₗ[R] Middle
  projection : Middle →ₗ[R] Right
  inclusion_injective : Function.Injective inclusion
  exact : Function.Exact inclusion projection
  projection_surjective : Function.Surjective projection

/-! ## W2: the two unsplit exact sequences of the filtration -/

/-- The canonical inclusion `B → Z`. -/
def boundaryInclusion (cell : CohomologyExactCell K Vprev V Vnext) :
    cell.B →ₗ[K] cell.Z :=
  Submodule.inclusion cell.B_le_Z

/-- The canonical quotient projection `Z → H`. -/
def cohomologyProjection (cell : CohomologyExactCell K Vprev V Vnext) :
    cell.Z →ₗ[K] cell.H :=
  cell.BInZ.mkQ

/-- The first canonical short exact sequence `0 → B → Z → H → 0`. -/
def boundaryCycleCohomologySequence
    (cell : CohomologyExactCell K Vprev V Vnext) :
    LinearShortExactSequence K cell.B cell.Z cell.H where
  inclusion := cell.boundaryInclusion
  projection := cell.cohomologyProjection
  inclusion_injective := Submodule.inclusion_injective cell.B_le_Z
  exact := by
    change Function.Exact
      (Submodule.inclusion cell.B_le_Z) cell.BInZ.mkQ
    rw [LinearMap.exact_iff, Submodule.ker_mkQ,
      Submodule.range_inclusion]
    rfl
  projection_surjective := Submodule.mkQ_surjective _

/-- The canonical inclusion `Z → C`. -/
def cycleInclusion (cell : CohomologyExactCell K Vprev V Vnext) :
    cell.Z →ₗ[K] V :=
  cell.Z.subtype

/-- The canonical outgoing projection `C → Bout`, namely the range-restricted
next differential. -/
def outgoingProjection (cell : CohomologyExactCell K Vprev V Vnext) :
    V →ₗ[K] cell.Bout :=
  cell.dNext.rangeRestrict

/-- The second canonical short exact sequence `0 → Z → C → Bout → 0`. -/
def cycleCochainOutgoingSequence
    (cell : CohomologyExactCell K Vprev V Vnext) :
    LinearShortExactSequence K cell.Z V cell.Bout where
  inclusion := cell.cycleInclusion
  projection := cell.outgoingProjection
  inclusion_injective := Submodule.subtype_injective _
  exact := by
    change Function.Exact cell.Z.subtype cell.dNext.rangeRestrict
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict,
      Submodule.range_subtype]
    rfl
  projection_surjective := LinearMap.surjective_rangeRestrict _

section FiniteDimensional

variable [FiniteDimensional K Vprev] [FiniteDimensional K V]
  [FiniteDimensional K Vnext]

omit [FiniteDimensional K Vprev] [FiniteDimensional K Vnext] in
/-- The boundary/cohomology part of the cell ledger. -/
theorem finrank_B_add_finrank_H
    (cell : CohomologyExactCell K Vprev V Vnext) :
    Module.finrank K cell.B + Module.finrank K cell.H =
      Module.finrank K cell.Z := by
  let e := Submodule.comapSubtypeEquivOfLe cell.B_le_Z
  have he : Module.finrank K cell.BInZ = Module.finrank K cell.B := by
    change Module.finrank K (cell.B.comap cell.Z.subtype) =
      Module.finrank K cell.B
    exact e.finrank_eq
  calc
    Module.finrank K cell.B + Module.finrank K cell.H =
        Module.finrank K cell.H + Module.finrank K cell.BInZ := by
          rw [he]
          exact Nat.add_comm _ _
    _ = Module.finrank K cell.Z :=
      Submodule.finrank_quotient_add_finrank cell.BInZ

omit [FiniteDimensional K Vprev] [FiniteDimensional K Vnext] in
/-- **Cell ledger.** Every cochain is inherited flow, unresolved cohomology
credit, or outgoing action, counted without choosing a splitting:

`finrank B + finrank H + finrank Bout = finrank C`. -/
theorem finrank_cell_ledger
    (cell : CohomologyExactCell K Vprev V Vnext) :
    Module.finrank K cell.B + Module.finrank K cell.H +
        Module.finrank K cell.Bout = Module.finrank K V := by
  calc
    Module.finrank K cell.B + Module.finrank K cell.H +
        Module.finrank K cell.Bout =
        Module.finrank K cell.Z + Module.finrank K cell.Bout := by
          rw [cell.finrank_B_add_finrank_H]
    _ = Module.finrank K cell.Bout + Module.finrank K cell.Z :=
      Nat.add_comm _ _
    _ = Module.finrank K V :=
      cell.dNext.finrank_range_add_finrank_ker

/-- The literal conservation-ledger instance, with cohomology seated in the
credit column.  Its projections are definitional; its conservation proof is
the propositional cell ledger above. -/
def finrankLedger
    (cell : CohomologyExactCell K Vprev V Vnext) : Ledger ℕ where
  stock := Module.finrank K cell.B
  credit := Module.finrank K cell.H
  converted := Module.finrank K cell.Bout
  total := Module.finrank K V
  conservation := cell.finrank_cell_ledger

omit [FiniteDimensional K Vprev] [FiniteDimensional K Vnext] in
@[simp] theorem finrankLedger_stock
    (cell : CohomologyExactCell K Vprev V Vnext) :
    cell.finrankLedger.stock = Module.finrank K cell.B := rfl

omit [FiniteDimensional K Vprev] [FiniteDimensional K Vnext] in
@[simp] theorem finrankLedger_credit
    (cell : CohomologyExactCell K Vprev V Vnext) :
    cell.finrankLedger.credit = Module.finrank K cell.H := rfl

omit [FiniteDimensional K Vprev] [FiniteDimensional K Vnext] in
@[simp] theorem finrankLedger_converted
    (cell : CohomologyExactCell K Vprev V Vnext) :
    cell.finrankLedger.converted = Module.finrank K cell.Bout := rfl

omit [FiniteDimensional K Vprev] [FiniteDimensional K Vnext] in
@[simp] theorem finrankLedger_total
    (cell : CohomologyExactCell K Vprev V Vnext) :
    cell.finrankLedger.total = Module.finrank K V := rfl

/-- The unsorted input stock before its boundary, cohomology, and outgoing
columns are observed. -/
def rawFinrankLedger
    (_cell : CohomologyExactCell K Vprev V Vnext) : Ledger ℕ where
  stock := Module.finrank K V
  credit := 0
  converted := 0
  total := Module.finrank K V
  conservation := by simp

/-- Sorting the cochain cell is an actual accounted transfer: outgoing rank
is spent from the raw available stock and appears in the converted column,
while `B` and `H` retain the remaining available balance. -/
def finrankTransfer
    (cell : CohomologyExactCell K Vprev V Vnext) : Transfer ℕ where
  before := cell.rawFinrankLedger
  after := cell.finrankLedger
  spent := Module.finrank K cell.Bout
  before_conserved := Ledger.conservation_identity _
  after_conserved := Ledger.conservation_identity _
  total_preserved := rfl
  available_decomposition := by
    simpa only [rawFinrankLedger, finrankLedger, Nat.add_zero] using
      cell.finrank_cell_ledger.symm
  converted_decomposition := by simp [rawFinrankLedger, finrankLedger]

/-! ## Additive invariants: exact filtration → K0 ledger → number -/

/-- A finite-dimensional additive invariant assigns a value to every finite
vector space and is additive on every short exact sequence.

The definition quantifies over *all* unsplit sequences; it contains no
complement choice. -/
structure AdditiveInvariant (A : Type uA) [AddCommMonoid A] where
  observe : (M : Type uV) → [AddCommGroup M] → [Module K M] →
    [FiniteDimensional K M] → A
  additive : ∀ {Left Middle Right : Type uV}
    [AddCommGroup Left] [Module K Left] [FiniteDimensional K Left]
    [AddCommGroup Middle] [Module K Middle] [FiniteDimensional K Middle]
    [AddCommGroup Right] [Module K Right] [FiniteDimensional K Right],
    (sequence : LinearShortExactSequence K Left Middle Right) →
      observe Middle = observe Left + observe Right

variable {A : Type uA} [AddCommMonoid A]

omit [FiniteDimensional K Vprev] in
/-- Any additive invariant turns the two exact filtration rows into the
three-column K0 ledger identity. -/
theorem invariant_ledger_identity
    (cell : CohomologyExactCell K Vprev V Vnext)
    (invariant : AdditiveInvariant (K := K) A) :
    invariant.observe cell.B + invariant.observe cell.H +
        invariant.observe cell.Bout = invariant.observe V := by
  have h₁ := invariant.additive cell.boundaryCycleCohomologySequence
  have h₂ := invariant.additive cell.cycleCochainOutgoingSequence
  calc
    invariant.observe cell.B + invariant.observe cell.H +
        invariant.observe cell.Bout =
        invariant.observe cell.Z + invariant.observe cell.Bout := by
          rw [← h₁]
    _ = invariant.observe V := h₂.symm

/-- The K0 identity observed in the repository's literal ledger carrier. -/
def invariantLedger
    (cell : CohomologyExactCell K Vprev V Vnext)
    (invariant : AdditiveInvariant (K := K) A) : Ledger A where
  stock := invariant.observe cell.B
  credit := invariant.observe cell.H
  converted := invariant.observe cell.Bout
  total := invariant.observe V
  conservation := cell.invariant_ledger_identity invariant

/-- Finrank is the first numerical observer of the exact filtration. -/
def finrankInvariant : AdditiveInvariant (K := K) ℕ where
  observe M := Module.finrank K M
  additive := fun sequence => by
    have h := sequence.projection.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr sequence.projection_surjective,
      finrank_top,
      LinearMap.exact_iff.mp sequence.exact,
      sequence.inclusion.finrank_range_of_inj
        sequence.inclusion_injective] at h
    simpa [Nat.add_comm] using h.symm

/-- Module length is a second observer.  Over a field it agrees with
finrank, but it is phrased through the exact-sequence length theorem and is
the form that extends to finite-length modules over general rings. -/
def lengthInvariant : AdditiveInvariant (K := K) ℕ∞ where
  observe M := Module.length K M
  additive := fun sequence =>
    Module.length_eq_add_of_exact sequence.inclusion sequence.projection
      sequence.inclusion_injective sequence.projection_surjective
      sequence.exact

end FiniteDimensional

/-! ## The finite-field cardinality observer -/

variable {p : ℕ} [Fact p.Prime]

/-- For a finite-dimensional `ZMod p`-space, the `p`-adic valuation of its
cardinality is exactly its finrank. -/
theorem padicValNat_natCard_eq_finrank
    (M : Type uV) [AddCommGroup M] [Module (ZMod p) M]
    [FiniteDimensional (ZMod p) M] :
    padicValNat p (Nat.card M) = Module.finrank (ZMod p) M := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := M), Nat.card_zmod,
    padicValNat.pow _ (Fact.out : p.Prime).ne_zero,
    padicValNat_self, Nat.mul_one]

/-- The `p`-adic cardinality of a finite vector space is an additive observer
on short exact sequences.  It records multiplicative group cardinality as an
additive ledger value. -/
def padicCardinalityInvariant :
    AdditiveInvariant (K := ZMod p) ℕ where
  observe M := padicValNat p (Nat.card M)
  additive := fun sequence => by
    rw [padicValNat_natCard_eq_finrank,
      padicValNat_natCard_eq_finrank,
      padicValNat_natCard_eq_finrank]
    exact (finrankInvariant (K := ZMod p)).additive sequence

/-! ## W3: automatic cohomological theorems -/

open scoped BigOperators

/-- A finite cochain-ledger profile.  `transfer i` is simultaneously the
outgoing boundary rank/value of degree `i` and the incoming boundary
rank/value of degree `i+1`.  The endpoint and middle equations are precisely
the local cohomology ledgers after subtracting the credit column. -/
structure EulerPoincareProfile (n : ℕ) (A : Type uA) [AddCommGroup A] where
  cochains : Fin (n + 2) → A
  cohomology : Fin (n + 2) → A
  transfer : Fin (n + 1) → A
  first : cochains 0 - cohomology 0 = transfer 0
  middle : ∀ i : Fin n,
    cochains i.succ.castSucc - cohomology i.succ.castSucc =
      transfer i.castSucc + transfer i.succ
  last : cochains (Fin.last _) - cohomology (Fin.last _) =
    transfer (Fin.last _)

namespace EulerPoincareProfile

variable {n : ℕ} {A : Type uA} [AddCommGroup A]

/-- Internal boundary transfers cancel pairwise in the alternating sum. -/
theorem internal_transfers_cancel (profile : EulerPoincareProfile n A) :
    ∑ i, (-1 : ℤ) ^ i.val •
      (profile.cochains i - profile.cohomology i) = 0 :=
  Fin.sum_neg_one_pow_eq_zero _ profile.transfer profile.first
    profile.middle profile.last

/-- **Euler--Poincare.** The alternating observation of a finite cochain
ladder equals the alternating observation of its cohomology.  For the
finrank observer this is the usual equation `chi(C) = chi(H)`; the proof is
the pairwise cancellation of every internal transfer above. -/
theorem eulerPoincare (profile : EulerPoincareProfile n A) :
    (∑ i, (-1 : ℤ) ^ i.val • profile.cochains i) =
      ∑ i, (-1 : ℤ) ^ i.val • profile.cohomology i := by
  have h := profile.internal_transfers_cancel
  simp_rw [smul_sub, Finset.sum_sub_distrib] at h
  exact sub_eq_zero.mp h

end EulerPoincareProfile

/-! ### Homotopy invariance on the executable cell -/

variable {Wprev W Wnext : Type uV}
  [AddCommGroup Wprev] [Module K Wprev]
  [AddCommGroup W] [Module K W]
  [AddCommGroup Wnext] [Module K Wnext]

/-- A morphism of three-term cochain cells. -/
structure CellMap
    (source : CohomologyExactCell K Vprev V Vnext)
    (target : CohomologyExactCell K Wprev W Wnext) where
  previous : Vprev →ₗ[K] Wprev
  middle : V →ₗ[K] W
  next : Vnext →ₗ[K] Wnext
  commutes_previous :
    middle.comp source.dPrev = target.dPrev.comp previous
  commutes_next :
    target.dNext.comp middle = next.comp source.dNext

namespace CellMap

variable {source : CohomologyExactCell K Vprev V Vnext}
  {target : CohomologyExactCell K Wprev W Wnext}

/-- A cell map restricts to a map on cycles. -/
def cycles (map : CellMap source target) : source.Z →ₗ[K] target.Z :=
  (map.middle.domRestrict source.Z).codRestrict target.Z fun cycle => by
    have hz := cycle.2
    change source.dNext cycle.1 = 0 at hz
    have h := LinearMap.congr_fun map.commutes_next cycle.1
    change target.dNext (map.middle cycle.1) =
      map.next (source.dNext cycle.1) at h
    change target.dNext (map.middle cycle.1) = 0
    simpa [hz] using h

/-- Boundaries are sent to boundaries, so the cycle map descends to the
cohomology quotient. -/
theorem maps_boundaries (map : CellMap source target) :
    source.BInZ ≤ target.BInZ.comap map.cycles := by
  intro boundary hboundary
  change map.middle boundary.1 ∈ target.B
  change boundary.1 ∈ source.B at hboundary
  rcases hboundary with ⟨x, hx⟩
  refine ⟨map.previous x, ?_⟩
  have h := LinearMap.congr_fun map.commutes_previous x
  change map.middle (source.dPrev x) =
    target.dPrev (map.previous x) at h
  rw [← h, hx]

/-- The induced map on cohomology. -/
def onCohomology (map : CellMap source target) : source.H →ₗ[K] target.H :=
  source.BInZ.mapQ target.BInZ map.cycles map.maps_boundaries

end CellMap

/-- A cochain homotopy in the middle degree.  Its two summands are the area
fillers `d h` and `h d`; no equality of routes is assumed before this
explicit filler is supplied. -/
structure CellHomotopy
    {source : CohomologyExactCell K Vprev V Vnext}
    {target : CohomologyExactCell K Wprev W Wnext}
    (f g : CellMap source target) where
  previous : V →ₗ[K] Wprev
  next : Vnext →ₗ[K] W
  middle_difference :
    f.middle - g.middle =
      target.dPrev.comp previous + next.comp source.dNext

namespace CellHomotopy

variable {source : CohomologyExactCell K Vprev V Vnext}
  {target : CohomologyExactCell K Wprev W Wnext}
  {f g : CellMap source target}

/-- **Homotopy invariance.** Route differences filled by `d h + h d` induce
the same map on the unresolved potential class `H`. -/
theorem onCohomology_eq (homotopy : CellHomotopy f g) :
    f.onCohomology = g.onCohomology := by
  apply Submodule.linearMap_qext
  ext cycle
  apply (Submodule.Quotient.eq target.BInZ).mpr
  change f.middle cycle.1 - g.middle cycle.1 ∈ target.B
  have hz := cycle.2
  change source.dNext cycle.1 = 0 at hz
  have h := LinearMap.congr_fun homotopy.middle_difference cycle.1
  change f.middle cycle.1 - g.middle cycle.1 =
    target.dPrev (homotopy.previous cycle.1) +
      homotopy.next (source.dNext cycle.1) at h
  rw [hz, map_zero, add_zero] at h
  exact ⟨homotopy.previous cycle.1, h.symm⟩

end CellHomotopy

/-! ### Euler additivity across a short exact split -/

/-- Alternating observation is additive for a degreewise short exact
sequence.  The hypothesis is exactly what any `AdditiveInvariant.additive`
produces in each degree; no degreewise splitting maps are selected. -/
theorem shortExactEulerAdditivity
    {n : ℕ} {A : Type uA} [AddCommGroup A]
    (left middle right : Fin n → A)
    (degreewise : ∀ i, middle i = left i + right i) :
    (∑ i, (-1 : ℤ) ^ i.val • middle i) =
      (∑ i, (-1 : ℤ) ^ i.val • left i) +
        ∑ i, (-1 : ℤ) ^ i.val • right i := by
  simp_rw [degreewise, smul_add, Finset.sum_add_distrib]

end CohomologyExactCell

/-! ## The third major IsoConserve tunnel instance -/

namespace IsoConserveBridge

open CohomologyExactCell IsoConserveStatements

variable {K : Type uK} [DivisionRing K]
  {Vprev V Vnext : Type uV}
  [AddCommGroup Vprev] [Module K Vprev]
  [AddCommGroup V] [Module K V]
  [AddCommGroup Vnext] [Module K Vnext]
  [FiniteDimensional K Vprev] [FiniteDimensional K V]
  [FiniteDimensional K Vnext]

/-- The cohomology sorting transfer viewed as a scheduler balanced step. -/
def cohomologyBalancedStep
    (cell : CohomologyExactCell K Vprev V Vnext) : BalancedStep ℕ :=
  toBalancedStep cell.finrankTransfer

omit [FiniteDimensional K Vprev] [FiniteDimensional K Vnext] in
/-- Cohomology's literal ledger is carried through the same L1 tunnel as the
generic transfer and the place-indexed reciprocity ledger. -/
theorem cohomology_L1_conservation
    (cell : CohomologyExactCell K Vprev V Vnext) :
    Columns.accounted (toColumns cell.finrankLedger) =
      Columns.accounted (toColumns cell.rawFinrankLedger) :=
  transfer_L1_conservation cell.finrankTransfer

end IsoConserveBridge

end Fermat.Conservation
