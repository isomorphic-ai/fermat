/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The Transfer--IsoConserve tunnel

The two tunnel ends meet in this file.  Fermat's route-neutral accounted
`Transfer` maps to the vendored scheduler L1/Noether conservation shape, and
the scheduler-side Kummer--Noether `principalize` and `evidence` steps map back
to concrete Fermat transfers.  The column orientation is exactly the one used
by the scheduler source's one-process `asSys` embedding:

* `unitKernel` is Fermat/scheduler stock;
* `classStock` is Fermat/scheduler credit;
* `evidenceRank` is Fermat/scheduler converted evidence.

The L4 projection is proved separately at both endpoints.  It is not used as
a substitute for L1: L1 preserves the global accounted sum, while L4 identifies
the two available columns with their flow integral.
-/
import Fermat.Conservation.IsoConserveStatements
import Fermat.Conservation.AreaTransfer

namespace Fermat.Conservation.IsoConserveBridge

open IsoConserveStatements

variable {α : Type*} [AddCommMonoid α]

/-- Forget a Fermat ledger's carried total after retaining all three accounted
columns.  The total is recoverable from `Ledger.conservation_identity`. -/
def toColumns (ledger : Ledger α) : Columns α where
  stock := ledger.stock
  credit := ledger.credit
  converted := ledger.converted

/-- Rebuild the canonical literal ledger represented by aggregate scheduler
columns. -/
def ofColumns (state : Columns α) : Ledger α where
  stock := state.stock
  credit := state.credit
  converted := state.converted
  total := Columns.accounted state
  conservation := rfl

@[simp] theorem toColumns_ofColumns (state : Columns α) :
    toColumns (ofColumns state) = state :=
  rfl

@[simp] theorem ofColumns_toColumns (ledger : Ledger α) :
    ofColumns (toColumns ledger) = ledger := by
  cases ledger with
  | mk stock credit converted total conservation =>
      dsimp [ofColumns, toColumns, Columns.accounted] at *
      subst total
      rfl

section PayloadDictionary

variable {R : Type*} [CommRing R]

/-- The two visible payload coordinates carried by scheduler columns.

The first coordinate is the route-neutral available balance, so passing to
the payload shadow forgets how that balance was split between `stock` and
`credit`.  The second coordinate is the converted balance. -/
def columnsAbelian (state : Columns R) : Heis.Abelian R :=
  AreaTransfer.ledgerAbelian (ofColumns state)

/-- Lift scheduler columns to a Heisenberg payload with an explicitly chosen
central coordinate.  The columns do not determine that private coordinate. -/
def columnsPayload (state : Columns R) (central : R) : Heis R :=
  AreaTransfer.ledgerPayload (ofColumns state) central

/-- The payload dictionary relates scheduler columns to exactly their visible
Heisenberg projection.  It deliberately says nothing about the forgotten
stock/credit split or central coordinate. -/
def PayloadDictionary (state : Columns R) (payload : Heis R) : Prop :=
  Heis.abelianization payload = columnsAbelian state

/-- Forgetting the chosen central coordinate of `columnsPayload` gives
exactly the two-column abelian shadow. -/
theorem abelianization_columnsPayload (state : Columns R) (central : R) :
    Heis.abelianization (columnsPayload state central) =
      columnsAbelian state := by
  simpa only [columnsPayload, columnsAbelian] using
    AreaTransfer.ledgerPayload_abelianization (ofColumns state) central

/-- Forward dictionary direction: every chosen central lift represents its
source columns. -/
theorem columnsPayload_dictionary (state : Columns R) (central : R) :
    PayloadDictionary state (columnsPayload state central) :=
  abelianization_columnsPayload state central

/-- The visible first coordinate of a column payload is the combined
stock-plus-credit balance. -/
theorem columnsPayload_stock_credit (state : Columns R) (central : R) :
    state.stock + state.credit = (columnsPayload state central).a :=
  rfl

/-- Rebuild columns from a payload after supplying the stock/credit split
which abelianization necessarily forgot.  No claim is made about recovering
the payload's central coordinate. -/
def columnsOfPayload (payload : Heis R) (stock credit : R)
    (_hsplit : stock + credit = payload.a) : Columns R where
  stock := stock
  credit := credit
  converted := payload.b

/-- `columnsOfPayload` recovers precisely the abelian projection when its
explicit stock/credit split is valid. -/
theorem columnsAbelian_columnsOfPayload (payload : Heis R)
    (stock credit : R) (hsplit : stock + credit = payload.a) :
    columnsAbelian (columnsOfPayload payload stock credit hsplit) =
      Heis.abelianization payload := by
  cases payload with
  | mk a b c =>
      simp only [columnsAbelian, columnsOfPayload,
        AreaTransfer.ledgerAbelian, Transfer.available, ofColumns,
        Heis.abelianization]
      rw [hsplit]

/-- Reverse dictionary direction under the named, explicit stock/credit
split. -/
theorem columnsOfPayload_dictionary (payload : Heis R)
    (stock credit : R) (hsplit : stock + credit = payload.a) :
    PayloadDictionary (columnsOfPayload payload stock credit hsplit)
      payload := by
  unfold PayloadDictionary
  exact (columnsAbelian_columnsOfPayload payload stock credit hsplit).symm

/-- Lifting columns with any central coordinate and then using their original
stock/credit split returns the original columns exactly. -/
@[simp] theorem columnsOfPayload_columnsPayload
    (state : Columns R) (central : R) :
    columnsOfPayload (columnsPayload state central) state.stock state.credit
      (columnsPayload_stock_credit state central) = state := by
  cases state
  rfl

/-- With the forgotten split supplied and the original center retained, the
reverse dictionary also reconstructs the complete payload. -/
@[simp] theorem columnsPayload_columnsOfPayload
    (payload : Heis R) (stock credit : R)
    (hsplit : stock + credit = payload.a) :
    columnsPayload (columnsOfPayload payload stock credit hsplit) payload.c =
      payload := by
  cases payload with
  | mk a b c =>
      change (⟨stock + credit, b, c⟩ : Heis R) = ⟨a, b, c⟩
      rw [hsplit]

end PayloadDictionary

/-- Attach the cached integral used by the distinct L4 statement. -/
def toIntegralColumns (ledger : Ledger α) : IntegralColumns α where
  toColumns := toColumns ledger
  netFlowIntegral := Transfer.available ledger

/-- Every literal ledger has the expected L4 column projection. -/
theorem ledger_l4_projection (ledger : Ledger α) :
    L4Invariant (toIntegralColumns ledger) :=
  rfl

/-- L4 holds at both endpoints independently of the L1 transfer proof. -/
theorem transfer_l4_projections (transfer : Transfer α) :
    L4Invariant (toIntegralColumns transfer.before) ∧
      L4Invariant (toIntegralColumns transfer.after) :=
  ⟨ledger_l4_projection transfer.before,
    ledger_l4_projection transfer.after⟩

/-- Read a Fermat transaction as the scheduler's balanced aggregate step. -/
def toBalancedStep (transfer : Transfer α) : BalancedStep α where
  before := toColumns transfer.before
  after := toColumns transfer.after
  spent := transfer.spent
  available_decomposition := by
    simpa [toColumns] using transfer.available_decomposition
  converted_decomposition := by
    simpa [toColumns] using transfer.converted_decomposition

/-- The scheduler-shaped balanced relation together with the payload before
and after the step and the Heisenberg word composed on the right. -/
structure PayloadBalancedStep (α R : Type*) [AddCommMonoid α] [CommRing R]
    extends BalancedStep α where
  beforePayload : Heis R
  afterPayload : Heis R
  word : Heis R
  payload_decomposition : afterPayload = beforePayload * word

/-- Read an area-aware Fermat transaction as a scheduler balanced step while
retaining its full payload equation. -/
def toPayloadBalancedStep {R : Type*} [CommRing R]
    (transfer : AreaTransfer α R) : PayloadBalancedStep α R where
  toBalancedStep := toBalancedStep transfer.toTransfer
  beforePayload := transfer.beforePayload
  afterPayload := transfer.afterPayload
  word := transfer.word
  payload_decomposition := transfer.payload_decomposition

@[simp] theorem toPayloadBalancedStep_toBalancedStep
    {R : Type*} [CommRing R] (transfer : AreaTransfer α R) :
    (toPayloadBalancedStep transfer).toBalancedStep =
      toBalancedStep transfer.toTransfer :=
  rfl

@[simp] theorem toPayloadBalancedStep_before
    {R : Type*} [CommRing R] (transfer : AreaTransfer α R) :
    (toPayloadBalancedStep transfer).before =
      toColumns transfer.toTransfer.before :=
  rfl

@[simp] theorem toPayloadBalancedStep_after
    {R : Type*} [CommRing R] (transfer : AreaTransfer α R) :
    (toPayloadBalancedStep transfer).after =
      toColumns transfer.toTransfer.after :=
  rfl

@[simp] theorem toPayloadBalancedStep_spent
    {R : Type*} [CommRing R] (transfer : AreaTransfer α R) :
    (toPayloadBalancedStep transfer).spent = transfer.toTransfer.spent :=
  rfl

@[simp] theorem toPayloadBalancedStep_beforePayload
    {R : Type*} [CommRing R] (transfer : AreaTransfer α R) :
    (toPayloadBalancedStep transfer).beforePayload = transfer.beforePayload :=
  rfl

@[simp] theorem toPayloadBalancedStep_afterPayload
    {R : Type*} [CommRing R] (transfer : AreaTransfer α R) :
    (toPayloadBalancedStep transfer).afterPayload = transfer.afterPayload :=
  rfl

@[simp] theorem toPayloadBalancedStep_word
    {R : Type*} [CommRing R] (transfer : AreaTransfer α R) :
    (toPayloadBalancedStep transfer).word = transfer.word :=
  rfl

/-- Every Fermat transfer induces the scheduler's L1 equality. -/
theorem transfer_L1_conservation (transfer : Transfer α) :
    Columns.accounted (toColumns transfer.after) =
      Columns.accounted (toColumns transfer.before) :=
  (toBalancedStep transfer).L1_conservation

/-- Area-aware transfers inherit L1 conservation from their abelian
`Transfer` projection. -/
theorem areaTransfer_L1_conservation {R : Type*} [CommRing R]
    (transfer : AreaTransfer α R) :
    Columns.accounted (toColumns transfer.toTransfer.after) =
      Columns.accounted (toColumns transfer.toTransfer.before) :=
  transfer_L1_conservation transfer.toTransfer

/-- Every Fermat transfer is a step of the scheduler-shaped balanced relation. -/
theorem transfer_induces_scheduler_rel (transfer : Transfer α) :
    BalancedStep.Rel (toColumns transfer.before)
      (toColumns transfer.after) :=
  ⟨toBalancedStep transfer, rfl, rfl⟩

/-- The relation on Fermat ledgers generated by accounted transfers. -/
def TransferRel (before after : Ledger α) : Prop :=
  ∃ transfer : Transfer α,
    transfer.before = before ∧ transfer.after = after

/-- Transfer-induced steps conserve accounted charge in Noether's exact
relation shape. -/
theorem transferRel_conserved :
    Noether.ConservedBy (@TransferRel α _)
      (fun ledger => Columns.accounted (toColumns ledger)) := by
  intro before after hstep
  obtain ⟨transfer, rfl, rfl⟩ := hstep
  exact transfer_L1_conservation transfer

/-- Reconstruct a Fermat transfer from a scheduler balanced step.  This is the
general converse: unlike a bare L1 equality, `BalancedStep` retains `spent`
and both exact column decompositions. -/
def ofBalancedStep (step : BalancedStep α) : Transfer α where
  before := ofColumns step.before
  after := ofColumns step.after
  spent := step.spent
  before_conserved := Ledger.conservation_identity (ofColumns step.before)
  after_conserved := Ledger.conservation_identity (ofColumns step.after)
  total_preserved := by
    change Columns.accounted step.before = Columns.accounted step.after
    exact step.L1_conservation.symm
  available_decomposition := by
    simpa [ofColumns] using step.available_decomposition
  converted_decomposition := by
    simpa [ofColumns] using step.converted_decomposition

@[simp] theorem ofBalancedStep_before (step : BalancedStep α) :
    (ofBalancedStep step).before = ofColumns step.before :=
  rfl

@[simp] theorem ofBalancedStep_after (step : BalancedStep α) :
    (ofBalancedStep step).after = ofColumns step.after :=
  rfl

@[simp] theorem ofBalancedStep_spent (step : BalancedStep α) :
    (ofBalancedStep step).spent = step.spent :=
  rfl

@[simp] theorem ofBalancedStep_toBalancedStep_before
    (transfer : Transfer α) :
    (ofBalancedStep (toBalancedStep transfer)).before = transfer.before := by
  simp [toBalancedStep]

@[simp] theorem ofBalancedStep_toBalancedStep_after
    (transfer : Transfer α) :
    (ofBalancedStep (toBalancedStep transfer)).after = transfer.after := by
  simp [toBalancedStep]

@[simp] theorem ofBalancedStep_toBalancedStep_spent
    (transfer : Transfer α) :
    (ofBalancedStep (toBalancedStep transfer)).spent = transfer.spent :=
  rfl

/-- The general scheduler-to-Fermat-to-scheduler correspondence is exact. -/
@[simp] theorem toBalancedStep_ofBalancedStep (step : BalancedStep α) :
    toBalancedStep (ofBalancedStep step) = step := by
  cases step
  rfl

/-- The general Fermat-to-scheduler-to-Fermat correspondence is exact. -/
@[simp] theorem ofBalancedStep_toBalancedStep (transfer : Transfer α) :
    ofBalancedStep (toBalancedStep transfer) = transfer := by
  cases transfer
  simp [ofBalancedStep, toBalancedStep]

/-- Reconstruct an area-aware Fermat transfer from the scheduler-shaped
balanced payload step. -/
def ofPayloadBalancedStep {R : Type*} [CommRing R]
    (step : PayloadBalancedStep α R) : AreaTransfer α R where
  toTransfer := ofBalancedStep step.toBalancedStep
  beforePayload := step.beforePayload
  afterPayload := step.afterPayload
  word := step.word
  payload_decomposition := step.payload_decomposition

@[simp] theorem ofPayloadBalancedStep_toTransfer
    {R : Type*} [CommRing R] (step : PayloadBalancedStep α R) :
    (ofPayloadBalancedStep step).toTransfer =
      ofBalancedStep step.toBalancedStep :=
  rfl

@[simp] theorem ofPayloadBalancedStep_before
    {R : Type*} [CommRing R] (step : PayloadBalancedStep α R) :
    (ofPayloadBalancedStep step).toTransfer.before = ofColumns step.before :=
  rfl

@[simp] theorem ofPayloadBalancedStep_after
    {R : Type*} [CommRing R] (step : PayloadBalancedStep α R) :
    (ofPayloadBalancedStep step).toTransfer.after = ofColumns step.after :=
  rfl

@[simp] theorem ofPayloadBalancedStep_spent
    {R : Type*} [CommRing R] (step : PayloadBalancedStep α R) :
    (ofPayloadBalancedStep step).toTransfer.spent = step.spent :=
  rfl

@[simp] theorem ofPayloadBalancedStep_beforePayload
    {R : Type*} [CommRing R] (step : PayloadBalancedStep α R) :
    (ofPayloadBalancedStep step).beforePayload = step.beforePayload :=
  rfl

@[simp] theorem ofPayloadBalancedStep_afterPayload
    {R : Type*} [CommRing R] (step : PayloadBalancedStep α R) :
    (ofPayloadBalancedStep step).afterPayload = step.afterPayload :=
  rfl

@[simp] theorem ofPayloadBalancedStep_word
    {R : Type*} [CommRing R] (step : PayloadBalancedStep α R) :
    (ofPayloadBalancedStep step).word = step.word :=
  rfl

/-- The scheduler-to-Fermat-to-scheduler payload correspondence is exact. -/
@[simp] theorem toPayloadBalancedStep_ofPayloadBalancedStep
    {R : Type*} [CommRing R] (step : PayloadBalancedStep α R) :
    toPayloadBalancedStep (ofPayloadBalancedStep step) = step := by
  cases step
  simp [toPayloadBalancedStep, ofPayloadBalancedStep]

/-- The Fermat-to-scheduler-to-Fermat payload correspondence is exact. -/
@[simp] theorem ofPayloadBalancedStep_toPayloadBalancedStep
    {R : Type*} [CommRing R] (transfer : AreaTransfer α R) :
    ofPayloadBalancedStep (toPayloadBalancedStep transfer) = transfer := by
  cases transfer
  simp [toPayloadBalancedStep, ofPayloadBalancedStep]

namespace KummerNoether

abbrev SchedulerLedger := IsoConserveStatements.KummerNoether.Ledger
abbrev SchedulerStep := IsoConserveStatements.KummerNoether.Step

/-- Embed the scheduler Kummer ledger as a literal Fermat ledger. -/
def ofSchedulerLedger (state : SchedulerLedger) : Ledger ℕ :=
  ofColumns (IsoConserveStatements.KummerNoether.columns state)

/-- Read a natural-valued Fermat ledger in the scheduler's exact Kummer column
orientation. -/
def toSchedulerLedger (ledger : Ledger ℕ) : SchedulerLedger where
  classStock := ledger.credit
  unitKernel := ledger.stock
  evidenceRank := ledger.converted

@[simp] theorem ofSchedulerLedger_stock (state : SchedulerLedger) :
    (ofSchedulerLedger state).stock = state.unitKernel :=
  rfl

@[simp] theorem ofSchedulerLedger_credit (state : SchedulerLedger) :
    (ofSchedulerLedger state).credit = state.classStock :=
  rfl

@[simp] theorem ofSchedulerLedger_converted (state : SchedulerLedger) :
    (ofSchedulerLedger state).converted = state.evidenceRank :=
  rfl

@[simp] theorem ofSchedulerLedger_total (state : SchedulerLedger) :
    (ofSchedulerLedger state).total =
      IsoConserveStatements.KummerNoether.charge state := by
  simp [ofSchedulerLedger, ofColumns, Columns.accounted,
    IsoConserveStatements.KummerNoether.columns,
    IsoConserveStatements.KummerNoether.charge, Nat.add_comm,
    Nat.add_left_comm]

@[simp] theorem toSchedulerLedger_ofSchedulerLedger
    (state : SchedulerLedger) :
    toSchedulerLedger (ofSchedulerLedger state) = state := by
  cases state
  rfl

@[simp] theorem ofSchedulerLedger_toSchedulerLedger (ledger : Ledger ℕ) :
    ofSchedulerLedger (toSchedulerLedger ledger) = ledger := by
  simpa [ofSchedulerLedger, toSchedulerLedger,
    IsoConserveStatements.KummerNoether.columns, toColumns] using
      (ofColumns_toColumns ledger)

/-- The Fermat and scheduler aggregate-column adapters commute exactly. -/
@[simp] theorem toColumns_ofSchedulerLedger (state : SchedulerLedger) :
    toColumns (ofSchedulerLedger state) =
      IsoConserveStatements.KummerNoether.columns state :=
  toColumns_ofColumns _

/-- The Kummer adapter also commutes with the source's distinct L4 surface. -/
theorem schedulerLedger_l4_projection (state : SchedulerLedger) :
    L4Invariant
      (IsoConserveStatements.KummerNoether.integralColumns state) :=
  IsoConserveStatements.KummerNoether.l4_integral state

/-- The Fermat adapter and scheduler's Kummer L4 adapter are definitionally
the same column projection. -/
@[simp] theorem toIntegralColumns_ofSchedulerLedger (state : SchedulerLedger) :
    toIntegralColumns (ofSchedulerLedger state) =
      IsoConserveStatements.KummerNoether.integralColumns state :=
  rfl

/-- The balanced scheduler aggregate represented by `principalize`.  This is a
zero-spent route from class credit into unit stock. -/
def principalizeBalancedStep (c k r : ℕ) : BalancedStep ℕ where
  before := IsoConserveStatements.KummerNoether.columns ⟨c + 1, k, r⟩
  after := IsoConserveStatements.KummerNoether.columns ⟨c, k + 1, r⟩
  spent := 0
  available_decomposition := by
    simp [IsoConserveStatements.KummerNoether.columns]
    omega
  converted_decomposition := by
    simp [IsoConserveStatements.KummerNoether.columns]

/-- The balanced scheduler aggregate represented by `evidence`.  Exactly one
unit leaves stock and enters converted evidence. -/
def evidenceBalancedStep (c k r : ℕ) : BalancedStep ℕ where
  before := IsoConserveStatements.KummerNoether.columns ⟨c, k + 1, r⟩
  after := IsoConserveStatements.KummerNoether.columns ⟨c, k, r + 1⟩
  spent := 1
  available_decomposition := by
    simp [IsoConserveStatements.KummerNoether.columns]
    omega
  converted_decomposition := by
    simp [IsoConserveStatements.KummerNoether.columns]

/-- The concrete Fermat transfer represented by scheduler `principalize`. -/
def principalizeTransfer (c k r : ℕ) : Transfer ℕ :=
  ofBalancedStep (principalizeBalancedStep c k r)

/-- The concrete Fermat transfer represented by scheduler `evidence`. -/
def evidenceTransfer (c k r : ℕ) : Transfer ℕ :=
  ofBalancedStep (evidenceBalancedStep c k r)

@[simp] theorem principalizeTransfer_before (c k r : ℕ) :
    (principalizeTransfer c k r).before =
      ofSchedulerLedger ⟨c + 1, k, r⟩ :=
  rfl

@[simp] theorem principalizeTransfer_after (c k r : ℕ) :
    (principalizeTransfer c k r).after =
      ofSchedulerLedger ⟨c, k + 1, r⟩ :=
  rfl

@[simp] theorem principalizeTransfer_spent (c k r : ℕ) :
    (principalizeTransfer c k r).spent = 0 :=
  rfl

@[simp] theorem evidenceTransfer_before (c k r : ℕ) :
    (evidenceTransfer c k r).before =
      ofSchedulerLedger ⟨c, k + 1, r⟩ :=
  rfl

@[simp] theorem evidenceTransfer_after (c k r : ℕ) :
    (evidenceTransfer c k r).after =
      ofSchedulerLedger ⟨c, k, r + 1⟩ :=
  rfl

@[simp] theorem evidenceTransfer_spent (c k r : ℕ) :
    (evidenceTransfer c k r).spent = 1 :=
  rfl

/-- Existential theorem form of the scheduler-to-Fermat correspondence. -/
theorem schedulerStep_instantiates_transfer
    {before after : SchedulerLedger} (step : SchedulerStep before after) :
    ∃ transfer : Transfer ℕ,
      transfer.before = ofSchedulerLedger before ∧
        transfer.after = ofSchedulerLedger after := by
  cases step with
  | principalize c k r =>
      exact ⟨principalizeTransfer c k r, rfl, rfl⟩
  | evidence c k r =>
      exact ⟨evidenceTransfer c k r, rfl, rfl⟩

/-- Every natural-valued Fermat transfer induces the scheduler Kummer charge
equality, with the same post-before orientation as L1 and `ConservedBy`. -/
theorem transfer_schedulerCharge_conserved (transfer : Transfer ℕ) :
    IsoConserveStatements.KummerNoether.charge
        (toSchedulerLedger transfer.after) =
      IsoConserveStatements.KummerNoether.charge
        (toSchedulerLedger transfer.before) := by
  have hL1 := transfer_L1_conservation transfer
  simpa [toSchedulerLedger, toColumns, Columns.accounted,
    IsoConserveStatements.KummerNoether.charge, Nat.add_comm,
    Nat.add_left_comm] using hL1

/-- The Kummer-state relation induced by Fermat transfers. -/
def SchedulerTransferRel (before after : SchedulerLedger) : Prop :=
  ∃ transfer : Transfer ℕ,
    toSchedulerLedger transfer.before = before ∧
      toSchedulerLedger transfer.after = after

/-- Every Fermat transfer induces a Noether-conserved scheduler relation. -/
theorem schedulerTransferRel_conserved :
    Noether.ConservedBy SchedulerTransferRel
      IsoConserveStatements.KummerNoether.charge := by
  intro before after hstep
  obtain ⟨transfer, hbefore, hafter⟩ := hstep
  rw [← hbefore, ← hafter]
  exact transfer_schedulerCharge_conserved transfer

/-- The concrete scheduler-to-Transfer construction proves the same L1 charge
equality through Fermat's accounted transaction. -/
theorem schedulerStep_charge_conserved_via_transfer
    {before after : SchedulerLedger} (step : SchedulerStep before after) :
    IsoConserveStatements.KummerNoether.charge after =
      IsoConserveStatements.KummerNoether.charge before := by
  obtain ⟨transfer, hbefore, hafter⟩ :=
    schedulerStep_instantiates_transfer step
  have h := transfer_schedulerCharge_conserved transfer
  simpa [hbefore, hafter] using h

end KummerNoether

end Fermat.Conservation.IsoConserveBridge
