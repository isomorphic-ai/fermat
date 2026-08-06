/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The conditional conductor-59 Tate bridge

The generic tame and wild local pairing constructions live in
`TamePlacePairing`.  This file now takes only one bilinear reading at the
distinguished place above `59`; the complete `Finsupp` pairing is constructed
as its single supported column.  Consequently every tame/non-distinguished
row is a theorem, not a local-orthogonality premise.

Poitou--Tate detector existence, the comparison with the selected gauge, and
global reciprocity remain explicit interfaces.  No unconditional relation
(7a), endpoint, or transformer is asserted here.
-/
import Fermat.Conservation.TamePlacePairing
import Fermat.FiftyNine.Conservation.CommonActionStage
import Fermat.FiftyNine.Conservation.Instance

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.TateBridge

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.TatePairing
open Fermat.Conservation.TamePlacePairing
open Fermat.Conservation.TransverseAnnihilator
open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.StateFactorPair

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

universe uDelta uPlace uSelmer uDual uLamp

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

variable {ζ : K} {hζ : IsPrimitiveRoot ζ 59}
  {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}
  {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt 59) Delta}
  {Place : Type uPlace} {SelmerChi : Type uSelmer}
  {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra 59 Delta) DOmegaSelmerChiStar]
  [Module (Polynomial (ZMod 59)) DOmegaSelmerChiStar]
  {LampMode : Type uLamp} [AddCommGroup LampMode]
  [Module (Polynomial (ZMod 59)) LampMode]

/-- The ambient type of the selected place-indexed pairing. -/
abbrev LocalPairing :=
  TatePairing.PlaceIndexedLocalPairing 59 Delta omega chi Place
    SelmerChi DOmegaSelmerChiStar

/-- The sole remaining local pairing interface: one bilinear, `#`-adjoint
reading at the distinguished place above `59`. -/
abbrev WildLocalInterface (distinguishedPlace : Place) :=
  TamePlacePairing.WildLocalInterface 59 Delta omega chi Place
    SelmerChi DOmegaSelmerChiStar distinguishedPlace

/-! ## The selected supporter-prime lamp -/

/-- The only lamp data not already proved by the conductor-59 bank: a
polynomial action on the chosen lamp mode and its annihilation law. -/
structure SelectedLampAction (d : LampMode) where
  polynomial : Polynomial (ZMod 59)
  annihilates : Annihilates polynomial d

namespace SelectedLampAction

/-- The selected lamp action becomes the existing named lamp interface at
`q = 827 = 2 * 7 * 59 + 1`; both prime facts and the supporter equation are
already proved/computable in the bank. -/
def toLampTransverse (action : SelectedLampAction d) :
    LampTransverse (ZMod 59) LampMode 59
      Credit.attestationPrime 7 d where
  exponent_prime := by norm_num
  supporter_prime := Credit.attestationPrime_isPrime
  supporter_relation := by norm_num [Credit.attestationPrime]
  polynomial := action.polynomial
  annihilates := action.annihilates

end SelectedLampAction

/-! ## W2.2: one global detector; support is already constructed -/

/-- A Poitou--Tate detector with one lamp-selected place above 827.

There is no support field: `wild.toPlaceIndexedLocalPairing` has only the
distinguished column by construction.  In particular, the auxiliary tame
reading is already zero even though the lamp is used to construct the global
detector.  Detector existence itself remains an arithmetic interface. -/
structure TransverseDetector
    (distinguishedPlace : Place)
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode) where
  detector : DOmegaSelmerChiStar
  auxiliaryPlace : Place
  auxiliary_ne_distinguished : auxiliaryPlace ≠ distinguishedPlace
  distinguished_liesOver : placePrime distinguishedPlace = 59
  auxiliary_liesOver :
    placePrime auxiliaryPlace = Credit.attestationPrime
  lampAction : SelectedLampAction d
  lampRealization :
    LampMode →ₗ[Polynomial (ZMod 59)] DOmegaSelmerChiStar
  lamp_realizes_detector : lampRealization d = detector

namespace TransverseDetector

/-- The detector carries an actual instance of the repository's lamp
interface, rather than only the numeral naming its auxiliary prime. -/
def lamp
    {distinguishedPlace : Place}
    {wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace}
    {placePrime : Place → ℕ}
    {x : SelmerChi} {d : LampMode}
    (detector : TransverseDetector distinguishedPlace wild placePrime x d) :
    LampTransverse (ZMod 59) LampMode 59
      Credit.attestationPrime 7 d :=
  detector.lampAction.toLampTransverse

/-- The lamp is not a decorative prime annotation: its polynomial
annihilator transports through the named realization to the actual global
detector. -/
theorem lamp_annihilates_detector
    {distinguishedPlace : Place}
    {wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace}
    {placePrime : Place → ℕ}
    {x : SelmerChi} {d : LampMode}
    (detector : TransverseDetector distinguishedPlace wild placePrime x d) :
    Annihilates detector.lampAction.polynomial detector.detector := by
  change detector.lampAction.polynomial • detector.detector = 0
  calc
    detector.lampAction.polynomial • detector.detector =
        detector.lampAction.polynomial • detector.lampRealization d := by
          rw [detector.lamp_realizes_detector]
    _ = detector.lampRealization
          (detector.lampAction.polynomial • d) := by
          rw [map_smul]
    _ = detector.lampRealization 0 := by
          rw [detector.lampAction.annihilates]
    _ = 0 := map_zero detector.lampRealization

/-- Every detector reading away from the distinguished wild place is zero by
the constructed single-column support.  The auxiliary inequality is retained
in the statement only to match the historical two-reading audit shape. -/
theorem outside_reading_eq_zero
    {distinguishedPlace : Place}
    {wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace}
    {placePrime : Place → ℕ}
    {x : SelmerChi} {d : LampMode}
    (detector : TransverseDetector distinguishedPlace wild placePrime x d)
    (v : Place) (hv : v ≠ distinguishedPlace)
    (_haux : v ≠ detector.auxiliaryPlace) :
    wild.toPlaceIndexedLocalPairing.pairAt v x detector.detector = 0 :=
  wild.pairAt_eq_zero_of_ne hv x detector.detector

end TransverseDetector

/-- **INTERFACE — W2.2.** Poitou--Tate supplies a global detector after one
auxiliary lamp place is relaxed.  Pairing support is not part of this target:
it is already the single distinguished column. -/
def transverse_detector_exists
    (distinguishedPlace : Place)
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode) : Prop :=
  Nonempty (TransverseDetector distinguishedPlace wild placePrime x d)

/-- The one detector selected by the existential target.  The two remaining
W2 targets are indexed by this exact witness, so they cannot silently switch
detectors or demand a theorem about every possible detector. -/
noncomputable def chosenTransverseDetector
    (distinguishedPlace : Place)
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode)
    (hDetector : transverse_detector_exists distinguishedPlace wild
      placePrime x d) :
    TransverseDetector distinguishedPlace wild placePrime x d :=
  Classical.choice hDetector

/-! ## W2.1: the local reading is the selected difference gauge -/

/-- The typed comparison between a scalar local Tate reading and the
class-group-valued selected difference gauge.

The additive readout is necessary because the two expressions live in
different carriers.  `reflects_selected_zero` is deliberately restricted to
this selected gauge; without it, vanishing of a scalar coordinate would not
imply relation (7a). -/
structure GaugeComparison
    (pair : StateLinkedIdealPair hζ S hz)
    (distinguishedPlace : Place)
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode)
    (detector : TransverseDetector distinguishedPlace wild placePrime x d) where
  readout : AllocatedClass K →+ ZMod 59
  unit : (ZMod 59)ˣ
  pairing_eq_gauge :
    wild.toPlaceIndexedLocalPairing.pairAt
        distinguishedPlace x detector.detector =
      (unit : ZMod 59) *
        readout (pair.ledger.rootClass 0 + 58 • pair.ledger.rootClass 1)
  reflects_selected_zero :
    readout
        (Fermat.Conservation.CommonActionStage.differenceGauge
          (AllocatedClass K)
          (CommonActionStage.StateLinkedIdealPair.classObstruction pair)) = 0 →
      Fermat.Conservation.CommonActionStage.differenceGauge
          (AllocatedClass K)
          (CommonActionStage.StateLinkedIdealPair.classObstruction pair) = 0

namespace GaugeComparison

variable
  {pair : StateLinkedIdealPair hζ S hz}
  {distinguishedPlace : Place}
  {wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
    (Place := Place) (SelmerChi := SelmerChi)
    (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace}
  {placePrime : Place → ℕ}
  {x : SelmerChi} {d : LampMode}
  {detector : TransverseDetector distinguishedPlace wild placePrime x d}

/-- Cancellation of the unit in the local comparison kills the scalar
readout of the displayed relation-(7a) word. -/
theorem scalarGauge_eq_zero_of_local_reading_eq_zero
    (comparison : GaugeComparison pair distinguishedPlace wild
      placePrime x d detector)
    (hlocal : wild.toPlaceIndexedLocalPairing.pairAt
      distinguishedPlace x detector.detector = 0) :
    comparison.readout
        (pair.ledger.rootClass 0 + 58 • pair.ledger.rootClass 1) = 0 := by
  have hmul :
      (comparison.unit : ZMod 59) *
          comparison.readout
            (pair.ledger.rootClass 0 + 58 • pair.ledger.rootClass 1) = 0 := by
    rw [← comparison.pairing_eq_gauge]
    exact hlocal
  exact (mul_eq_zero.mp hmul).resolve_left (Units.ne_zero comparison.unit)

/-- Scalar local vanishing reflects back through the typed readout to zero
of the actual class-group difference gauge. -/
theorem gauge_eq_zero_of_local_reading_eq_zero
    (comparison : GaugeComparison pair distinguishedPlace wild
      placePrime x d detector)
    (hlocal : wild.toPlaceIndexedLocalPairing.pairAt
      distinguishedPlace x detector.detector = 0) :
    Fermat.Conservation.CommonActionStage.differenceGauge
        (AllocatedClass K)
        (CommonActionStage.StateLinkedIdealPair.classObstruction pair) = 0 := by
  apply comparison.reflects_selected_zero
  rw [CommonActionStage.StateLinkedIdealPair.differenceGauge_reading]
  exact comparison.scalarGauge_eq_zero_of_local_reading_eq_zero hlocal

end GaugeComparison

/-- **INTERFACE — W2.1.** The one detector selected by the named transverse
target admits a unit-valued comparison between its 59-local reading and the
already computed selected gauge, including the required zero-reflection
clause.  Indexing by `hDetector` makes the witness shared and prevents this
target from being vacuous when no global detector exists. -/
def gauge_eq_local_tate_pairing
    (pair : StateLinkedIdealPair hζ S hz)
    (distinguishedPlace : Place)
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode)
    (hDetector : transverse_detector_exists distinguishedPlace wild
      placePrime x d) : Prop :=
  Nonempty (GaugeComparison pair distinguishedPlace wild
    placePrime x d
      (chosenTransverseDetector distinguishedPlace wild
        placePrime x d hDetector))

/-! ## The proved bank and the explicit place-by-place audit -/

/-- **PROVEN bank receipts.** These are the exact statements supplied by the
existing conductor-59 cone.  They intentionally remain in their original
relative-index, real-unit, and ideal-class carriers. -/
structure N59BankReceipts (pair : StateLinkedIdealPair hζ S hz) where
  capacity : Credit.CapacityCertificateGoal hζ
  boundedSinnott : Credit.BoundedSinnottBridge hζ
  plusClassNumber :
    ¬59 ∣ NumberField.classNumber (NumberField.maximalRealSubfield K)
  deepFlow : Instance.DeepFlowLaw59 hζ
  repayment : ∀ {u : NumberField.IsCMField.realUnits K},
    Instance.IsDeeplyRepayable hζ u →
      Fermat.Conservation.Credit.Repayment.IsRepaid 59 u
  sevenD : pair.ledger.VandiverSevenD 0 1

/-- Assembly of all bank receipts from their existing proved declarations.
This theorem proves no localization or orthogonality statement. -/
def n59BankReceipts (pair : StateLinkedIdealPair hζ S hz) :
    N59BankReceipts pair where
  capacity := CapacityCertificate.capacityCertificate hζ
  boundedSinnott := Credit.boundedSinnottBridge hζ
  plusClassNumber := Fold.not_dvd_plusClassNumber (K := K)
  deepFlow := Instance.deepFlowLaw59 hζ
  repayment := fun hdeep => Instance.repayment_of_capacity_and_flow hζ hdeep
  sevenD :=
    StateFactorConjugation.StateLinkedIdealPair.vandiverSevenD pair

/-- The complete audit object behind `bank_silences_other_places`.

All existing conductor-59 bank receipts remain present as an auditable
record.  There are no local-orthogonality fields: the pairing itself has a
single supported column, so every row away from the distinguished place is
already proved. -/
structure BankSilenceAudit
    (pair : StateLinkedIdealPair hζ S hz)
    (distinguishedPlace : Place)
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode)
    (detector : TransverseDetector distinguishedPlace wild placePrime x d) where
  receipts : N59BankReceipts pair

namespace BankSilenceAudit

variable
  {pair : StateLinkedIdealPair hζ S hz}
  {distinguishedPlace : Place}
  {wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
    (Place := Place) (SelmerChi := SelmerChi)
    (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace}
  {placePrime : Place → ℕ}
  {x : SelmerChi} {d : LampMode}
  {detector : TransverseDetector distinguishedPlace wild placePrime x d}

/-- Audit row for the lamp-selected auxiliary place. -/
theorem auxiliary_reading_eq_zero
    (_audit : BankSilenceAudit pair distinguishedPlace wild
      placePrime x d detector) :
    wild.toPlaceIndexedLocalPairing.pairAt
      detector.auxiliaryPlace x detector.detector = 0 :=
  wild.pairAt_eq_zero_of_ne detector.auxiliary_ne_distinguished
    x detector.detector

/-- Audit row for an arbitrary place outside the distinguished/auxiliary
pair, discharged by the single-column support theorem. -/
theorem other_reading_eq_zero
    (_audit : BankSilenceAudit pair distinguishedPlace wild
      placePrime x d detector)
    (v : Place) (hv : v ≠ distinguishedPlace)
    (_haux : v ≠ detector.auxiliaryPlace) :
    wild.toPlaceIndexedLocalPairing.pairAt v x detector.detector = 0 :=
  wild.pairAt_eq_zero_of_ne hv x detector.detector

/-- The place-by-place audit silences every column other than the
distinguished one, including the auxiliary column as a separate case. -/
theorem away_reading_eq_zero
    (_audit : BankSilenceAudit pair distinguishedPlace wild
      placePrime x d detector)
    (v : Place) (hv : v ≠ distinguishedPlace) :
    wild.toPlaceIndexedLocalPairing.pairAt v x detector.detector = 0 :=
  wild.pairAt_eq_zero_of_ne hv x detector.detector

end BankSilenceAudit

/-- **PROVEN tame bank audit.** All selected bank receipts are assembled and
all non-59 columns are silent by the constructed single support. -/
def bank_silences_other_places
    (pair : StateLinkedIdealPair hζ S hz)
    (distinguishedPlace : Place)
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode)
    (hDetector : transverse_detector_exists distinguishedPlace wild
      placePrime x d) :
    BankSilenceAudit pair distinguishedPlace wild
    placePrime x d
      (chosenTransverseDetector distinguishedPlace wild
        placePrime x d hDetector) where
  receipts := n59BankReceipts pair

/-! ## W3: the compiled conditional implication -/

namespace StateLinkedIdealPair

/-- **PROVEN conditional master theorem.** The sole wild pairing interface
and reciprocity law, together with detector existence and the selected gauge
comparison, force the selected difference gauge to vanish and hence prove
relation (7a) through the existing exact gauge theorem.  The former bank
premise has been removed: its receipts and all away rows are now constructed
inside the proof.

This is deliberately not an unconditional `vandiverSevenA` declaration.
Its mod-59 depth limitation is recorded below as the named
`mu_59_to_the_n_risk`; the theorem does not claim that first-layer pairings
detect a class living deeper in the 59-power tower. -/
theorem vandiverSevenA_of_tate_bridge
    (pair : StateLinkedIdealPair hζ S hz)
    (distinguishedPlace : Place)
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    (reciprocity : TatePairing.GlobalReciprocityLaw
      wild.toPlaceIndexedLocalPairing)
    (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode)
    (hDetector : transverse_detector_exists distinguishedPlace wild
      placePrime x d)
    (hGauge : gauge_eq_local_tate_pairing pair distinguishedPlace wild
      placePrime x d hDetector) :
    pair.ledger.VandiverSevenA 0 1 := by
  let detector := chosenTransverseDetector distinguishedPlace wild
    placePrime x d hDetector
  change Nonempty (GaugeComparison pair distinguishedPlace wild
    placePrime x d detector) at hGauge
  rcases hGauge with ⟨comparison⟩
  let audit := bank_silences_other_places pair distinguishedPlace wild
    placePrime x d hDetector
  have hother : ∀ v, v ≠ distinguishedPlace →
      wild.toPlaceIndexedLocalPairing.pairAt v x detector.detector = 0 := by
    intro v hv
    exact audit.away_reading_eq_zero v hv
  have hlocal :
      wild.toPlaceIndexedLocalPairing.pairAt
        distinguishedPlace x detector.detector = 0 :=
    reciprocity.pairAt_eq_zero_of_other_places
      distinguishedPlace x detector.detector hother
  have hgauge := comparison.gauge_eq_zero_of_local_reading_eq_zero hlocal
  exact
    (CommonActionStage.StateLinkedIdealPair.differenceGauge_eq_zero_iff_vandiverSevenA
      pair).mp hgauge

end StateLinkedIdealPair

/-! ## Named depth risk -/

/-- The concrete information lost by reducing relation (7a) to the first
mod-59 layer: `58 = -1` modulo 59, but not modulo `59²`. -/
structure Mu59ToTheNRisk : Prop where
  mod59_discards_correction : (58 : ZMod 59) = -1
  mod59Squared_retains_correction : (58 : ZMod (59 ^ 2)) ≠ -1

/-- **NAMED RISK — `mu_59_to_the_n`.** If the relevant class lives deeper
than the mod-59 layer, a future arithmetic pairing must be `59^n`-valued (or
integrally lifted); otherwise the correction in `58 = -1 + 59` is discarded
rather than routed through the bank. -/
theorem mu_59_to_the_n_risk : Mu59ToTheNRisk := by
  constructor <;> decide

end Fermat.FiftyNine.Conservation.TateBridge
