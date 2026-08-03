/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Area-carrying accounted transfers

`AreaTransfer` is the degree-two additive lift of the existing route-neutral
`Transfer`.  Its old transaction is inherited, never duplicated; the extra
payload is composed on the right with the twisted Heisenberg law.  The ledger
carrier and payload ring are separate so existing natural-valued and
class-group transactions remain valid D=1 projections.
-/
import Fermat.Conservation.Heis
import Fermat.Conservation.Transfer

namespace Fermat.Conservation

/-- One endpoint carrying both its existing ledger columns and its D=2
payload. -/
structure AreaState (α R : Type*) [AddCommMonoid α] where
  columns : Ledger α
  payload : Heis R

/-- An existing accounted transaction together with its ordered Heisenberg
payload word.  The payload law is additive: it does not alter or replace the
underlying `Transfer`. -/
structure AreaTransfer (α R : Type*) [AddCommMonoid α] [CommRing R]
    extends Transfer α where
  beforePayload : Heis R
  afterPayload : Heis R
  word : Heis R
  payload_decomposition : afterPayload = beforePayload * word

namespace AreaTransfer

variable {α R : Type*} [AddCommMonoid α] [CommRing R]

omit [AddCommMonoid α] [CommRing R] in
private theorem heis_eq_of_coordinates {g h : Heis R}
    (ha : g.a = h.a) (hb : g.b = h.b) (hc : g.c = h.c) : g = h := by
  cases g
  cases h
  simp_all

omit [AddCommMonoid α] [CommRing R] in
private theorem abelian_eq_of_coordinates {x y : Heis.Abelian R}
    (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x
  cases y
  simp_all

/-- The source endpoint as the promised `(columns, payload)` pair. -/
def beforeState (transfer : AreaTransfer α R) : AreaState α R :=
  ⟨transfer.before, transfer.beforePayload⟩

/-- The target endpoint as the promised `(columns, payload)` pair. -/
def afterState (transfer : AreaTransfer α R) : AreaState α R :=
  ⟨transfer.after, transfer.afterPayload⟩

/-- Forget the D=2 payload.  This generated parent is the existing D=1
transaction, rather than a second conservation proof. -/
def abelianProjection (transfer : AreaTransfer α R) : Transfer α :=
  transfer.toTransfer

@[simp] theorem abelianProjection_before (transfer : AreaTransfer α R) :
    transfer.abelianProjection.before = transfer.before :=
  rfl

@[simp] theorem abelianProjection_after (transfer : AreaTransfer α R) :
    transfer.abelianProjection.after = transfer.after :=
  rfl

@[simp] theorem abelianProjection_spent (transfer : AreaTransfer α R) :
    transfer.abelianProjection.spent = transfer.spent :=
  rfl

/-- The identity area transfer at one payload-carrying endpoint. -/
def refl (columns : Ledger α) (payload : Heis R) : AreaTransfer α R where
  toTransfer := Transfer.refl columns
  beforePayload := payload
  afterPayload := payload
  word := 1
  payload_decomposition := (Heis.mul_one payload).symm

/-- Compose consecutive area transfers.  Both the ledger and payload endpoint
must link; the route word is ordered `first.word * second.word`, retaining the
cross term `first.word.a * second.word.b`. -/
def comp (first second : AreaTransfer α R)
    (hlink : first.afterState = second.beforeState) : AreaTransfer α R where
  toTransfer := Transfer.comp first.toTransfer second.toTransfer (by
    simpa [afterState, beforeState] using
      congrArg AreaState.columns hlink)
  beforePayload := first.beforePayload
  afterPayload := second.afterPayload
  word := first.word * second.word
  payload_decomposition := by
    have hpayload : first.afterPayload = second.beforePayload := by
      simpa [afterState, beforeState] using
        congrArg AreaState.payload hlink
    calc
      second.afterPayload = second.beforePayload * second.word :=
        second.payload_decomposition
      _ = first.afterPayload * second.word := by rw [← hpayload]
      _ = (first.beforePayload * first.word) * second.word := by
        rw [first.payload_decomposition]
      _ = first.beforePayload * (first.word * second.word) :=
        Heis.mul_assoc _ _ _

@[simp] theorem toTransfer_refl (columns : Ledger α) (payload : Heis R) :
    (refl columns payload).toTransfer = Transfer.refl columns :=
  rfl

@[simp] theorem toTransfer_comp (first second : AreaTransfer α R)
    (hlink : first.afterState = second.beforeState) :
    (comp first second hlink).toTransfer =
      Transfer.comp first.toTransfer second.toTransfer (by
        simpa [afterState, beforeState] using
          congrArg AreaState.columns hlink) :=
  rfl

/-! ## Chains and their D=1 projection -/

end AreaTransfer

namespace Transfer

variable {α : Type*} [AddCommMonoid α]

/-- A list of existing transfers whose adjacent ledger endpoints link. -/
inductive Chain : List (Transfer α) → Prop where
  | nil : Chain []
  | singleton (transfer : Transfer α) : Chain [transfer]
  | cons {first second : Transfer α} {rest : List (Transfer α)}
      (hlink : first.after = second.before)
      (tail : Chain (second :: rest)) : Chain (first :: second :: rest)

end Transfer

namespace AreaTransfer

variable {α R : Type*} [AddCommMonoid α] [CommRing R]

/-- A list of D=2 transfers whose adjacent `(columns, payload)` endpoints
link. -/
inductive Chain : List (AreaTransfer α R) → Prop where
  | nil : Chain []
  | singleton (transfer : AreaTransfer α R) : Chain [transfer]
  | cons {first second : AreaTransfer α R}
      {rest : List (AreaTransfer α R)}
      (hlink : first.afterState = second.beforeState)
      (tail : Chain (second :: rest)) : Chain (first :: second :: rest)

/-- Forgetting every payload in an area chain produces an existing Transfer
chain; no parallel conservation proof is introduced. -/
theorem chain_projects {transfers : List (AreaTransfer α R)}
    (chain : Chain transfers) :
    Transfer.Chain (transfers.map abelianProjection) := by
  induction chain with
  | nil => exact Transfer.Chain.nil
  | singleton transfer =>
      exact Transfer.Chain.singleton transfer.abelianProjection
  | cons hlink tail ih =>
      exact Transfer.Chain.cons (by
        simpa [afterState, beforeState] using
          congrArg AreaState.columns hlink) ih

/-! ## The existing Ledger as the D=1 endpoint shadow -/

variable {S : Type*} [CommRing S]

/-- The two route-neutral visible coordinates of an existing ledger:
spendable stock-plus-credit and converted receipt. -/
def ledgerAbelian (ledger : Ledger S) : Heis.Abelian S :=
  ⟨Transfer.available ledger, ledger.converted⟩

/-- Lift those same D=1 coordinates with an arbitrary retained area. -/
def ledgerPayload (ledger : Ledger S) (area : S) : Heis S :=
  ⟨Transfer.available ledger, ledger.converted, area⟩

/-- The old Ledger columns are exactly the abelianization of their canonical
payload lift. -/
theorem ledgerPayload_abelianization (ledger : Ledger S) (area : S) :
    Heis.abelianization (ledgerPayload ledger area) = ledgerAbelian ledger :=
  Heis.abelianization_mk _ _ _

/-- The two visible coordinates still sum to the Ledger's carried total. -/
theorem ledgerAbelian_sum_eq_total (ledger : Ledger S) :
    (ledgerAbelian ledger).a + (ledgerAbelian ledger).b = ledger.total := by
  change ledger.stock + ledger.credit + ledger.converted = ledger.total
  exact Ledger.conservation_identity ledger

/-- An area transfer over the same ring has the existing Ledger shadow at
both endpoints. -/
def HasLedgerShadow (transfer : AreaTransfer S S) : Prop :=
  Heis.abelianization transfer.beforePayload =
      ledgerAbelian transfer.before ∧
    Heis.abelianization transfer.afterPayload =
      ledgerAbelian transfer.after

/-- Canonically lift any signed existing Transfer.  The visible payload word
is `(-spent, spent)`; `wordArea` is its additional central contribution, and
the twisted cross term determines the target area. -/
def ofTransfer (transfer : Transfer S) (beforeArea wordArea : S) :
    AreaTransfer S S where
  toTransfer := transfer
  beforePayload := ledgerPayload transfer.before beforeArea
  afterPayload := ledgerPayload transfer.after
    (beforeArea + wordArea +
      Transfer.available transfer.before * transfer.spent)
  word := ⟨-transfer.spent, transfer.spent, wordArea⟩
  payload_decomposition := by
    apply heis_eq_of_coordinates
    · change Transfer.available transfer.after =
        Transfer.available transfer.before + -transfer.spent
      rw [transfer.available_eq]
      ring
    · exact transfer.converted_decomposition
    · rfl

@[simp] theorem ofTransfer_toTransfer (transfer : Transfer S)
    (beforeArea wordArea : S) :
    (ofTransfer transfer beforeArea wordArea).toTransfer = transfer :=
  rfl

/-- The canonical lift really has the old Ledger as both endpoint shadows. -/
theorem ofTransfer_hasLedgerShadow (transfer : Transfer S)
    (beforeArea wordArea : S) :
    HasLedgerShadow (ofTransfer transfer beforeArea wordArea) :=
  ⟨ledgerPayload_abelianization _ _, ledgerPayload_abelianization _ _⟩

/-- The canonical word's D=1 projection is the exact signed displacement of
the existing transaction. -/
theorem ofTransfer_word_abelianization (transfer : Transfer S)
    (beforeArea wordArea : S) :
    Heis.abelianization (ofTransfer transfer beforeArea wordArea).word =
      (⟨-transfer.spent, transfer.spent⟩ : Heis.Abelian S) :=
  Heis.abelianization_mk _ _ _

/-- Linked composition preserves the endpoint-shadow condition. -/
theorem comp_hasLedgerShadow (first second : AreaTransfer S S)
    (hlink : first.afterState = second.beforeState)
    (hfirst : HasLedgerShadow first) (hsecond : HasLedgerShadow second) :
    HasLedgerShadow (comp first second hlink) :=
  ⟨hfirst.1, hsecond.2⟩

/-- For every coherent area transfer, the payload word abelianizes to the
signed displacement already forced by its inherited Transfer.  This is the
compiled statement that the D=1 transaction is the endpoint shadow of D=2. -/
theorem word_abelianization_of_hasLedgerShadow
    (transfer : AreaTransfer S S) (hshadow : HasLedgerShadow transfer) :
    Heis.abelianization transfer.word =
      (⟨-transfer.spent, transfer.spent⟩ : Heis.Abelian S) := by
  have hpayloadA := congrArg Heis.a transfer.payload_decomposition
  have hpayloadB := congrArg Heis.b transfer.payload_decomposition
  change transfer.afterPayload.a =
    transfer.beforePayload.a + transfer.word.a at hpayloadA
  change transfer.afterPayload.b =
    transfer.beforePayload.b + transfer.word.b at hpayloadB
  have hbeforeA := congrArg Heis.Abelian.a hshadow.1
  have hbeforeB := congrArg Heis.Abelian.b hshadow.1
  have hafterA := congrArg Heis.Abelian.a hshadow.2
  have hafterB := congrArg Heis.Abelian.b hshadow.2
  change transfer.beforePayload.a =
    Transfer.available transfer.before at hbeforeA
  change transfer.beforePayload.b = transfer.before.converted at hbeforeB
  change transfer.afterPayload.a =
    Transfer.available transfer.after at hafterA
  change transfer.afterPayload.b = transfer.after.converted at hafterB
  rw [hbeforeA, hafterA] at hpayloadA
  rw [hbeforeB, hafterB] at hpayloadB
  have hsum : (0 : S) = transfer.spent + transfer.word.a := by
    apply add_left_cancel (a := Transfer.available transfer.after)
    calc
      Transfer.available transfer.after + 0 =
          Transfer.available transfer.after := add_zero _
      _ = Transfer.available transfer.before + transfer.word.a := hpayloadA
      _ = (Transfer.available transfer.after + transfer.spent) +
          transfer.word.a := by rw [transfer.available_eq]
      _ = Transfer.available transfer.after +
          (transfer.spent + transfer.word.a) := add_assoc _ _ _
  have hwordA : transfer.word.a = -transfer.spent := by
    calc
      transfer.word.a = 0 + transfer.word.a := (zero_add _).symm
      _ = (-transfer.spent + transfer.spent) + transfer.word.a := by
        rw [neg_add_cancel]
      _ = -transfer.spent + (transfer.spent + transfer.word.a) :=
        add_assoc _ _ _
      _ = -transfer.spent + 0 := by rw [← hsum]
      _ = -transfer.spent := add_zero _
  have hwordB : transfer.word.b = transfer.spent := by
    apply add_left_cancel (a := transfer.before.converted)
    calc
      transfer.before.converted + transfer.word.b =
          transfer.after.converted := hpayloadB.symm
      _ = transfer.before.converted + transfer.spent :=
        transfer.converted_decomposition
  apply abelian_eq_of_coordinates hwordA hwordB

/-! ## Structural no-erasure and exact cancellation -/

/-- Every admissible area word acts injectively on private central inputs: no
composition can represent a constant erasure map. -/
theorem no_erasure (transfer : AreaTransfer α R) :
    Function.Injective (fun c : R ↦ Heis.center c * transfer.word) :=
  Heis.no_private_drain transfer.word

/-- In particular, the same admissible composition cannot identify a nonzero
private central input with the zero input. -/
theorem nonzero_center_not_erased (transfer : AreaTransfer α R)
    {c : R} (hc : c ≠ 0) :
    Heis.center c * transfer.word ≠
      Heis.center 0 * transfer.word := by
  intro h
  exact hc (transfer.no_erasure h)

/-- A chosen central coordinate can vanish only by the honest pairing law:
the word contributes its exact additive opposite. -/
theorem central_coordinate_eq_zero_iff_exact_cancellation
    (transfer : AreaTransfer α R) (c : R) :
    (Heis.center c * transfer.word).c = 0 ↔ transfer.word.c = -c :=
  Heis.central_coordinate_eq_zero_iff_exact_cancellation transfer.word c

end AreaTransfer

end Fermat.Conservation
