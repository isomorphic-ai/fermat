/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The conditional conductor-59 Tate bridge

The generic local pairing and reciprocity laws live in `TatePairing`.  This
file states the three remaining conductor-59 arithmetic targets on one
shared detector, records exactly which bank receipts already exist, and
compiles the conditional route from those inputs to relation (7a).

No value of any of the three target propositions is asserted here.  In
particular, the bank receipts do not silently become localization theorems:
every local vanishing still passes through an explicit orthogonality guard.
-/
import Fermat.Conservation.TatePairing
import Fermat.FiftyNine.Conservation.CommonActionStage
import Fermat.FiftyNine.Conservation.Instance

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.TateBridge

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.TatePairing
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

/-- The selected specialization of the generic local-pairing interface. -/
abbrev LocalPairing :=
  TatePairing.PlaceIndexedLocalPairing 59 Delta omega chi Place
    SelmerChi DOmegaSelmerChiStar

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

/-! ## W2.2: one global detector with two possible readings -/

/-- A Poitou--Tate detector whose only possible nonzero readings are the
distinguished place above 59 and one lamp-selected place above 827.

The support statement is containment, not equality: the bank is intended to
kill the auxiliary coordinate, so demanding that coordinate be nonzero would
make the three hypotheses inconsistent.  No value of this structure is
constructed in the current cone. -/
structure TransverseDetector
    (pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar))
    (distinguishedPlace : Place) (placePrime : Place → ℕ)
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
  outside_two_readings : ∀ v,
    v ≠ distinguishedPlace → v ≠ auxiliaryPlace →
      pairing.pairAt v x detector = 0

namespace TransverseDetector

/-- The detector carries an actual instance of the repository's lamp
interface, rather than only the numeral naming its auxiliary prime. -/
def lamp
    {pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)}
    {distinguishedPlace : Place} {placePrime : Place → ℕ}
    {x : SelmerChi} {d : LampMode}
    (detector : TransverseDetector pairing distinguishedPlace placePrime x d) :
    LampTransverse (ZMod 59) LampMode 59
      Credit.attestationPrime 7 d :=
  detector.lampAction.toLampTransverse

/-- The lamp is not a decorative prime annotation: its polynomial
annihilator transports through the named realization to the actual global
detector. -/
theorem lamp_annihilates_detector
    {pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)}
    {distinguishedPlace : Place} {placePrime : Place → ℕ}
    {x : SelmerChi} {d : LampMode}
    (detector : TransverseDetector pairing distinguishedPlace placePrime x d) :
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

/-- Named support-containment projection recording the detector's two-place
Poitou--Tate condition. -/
theorem outside_reading_eq_zero
    {pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)}
    {distinguishedPlace : Place} {placePrime : Place → ℕ}
    {x : SelmerChi} {d : LampMode}
    (detector : TransverseDetector pairing distinguishedPlace placePrime x d)
    (v : Place) (hv : v ≠ distinguishedPlace)
    (haux : v ≠ detector.auxiliaryPlace) :
    pairing.pairAt v x detector.detector = 0 :=
  detector.outside_two_readings v hv haux

end TransverseDetector

/-- **INTERFACE — W2.2.** Poitou--Tate supplies a global detector after one
auxiliary lamp place is relaxed.  Its two possible readings are at the place
above 59 and the place above the selected supporter prime 827. -/
def transverse_detector_exists
    (pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar))
    (distinguishedPlace : Place) (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode) : Prop :=
  Nonempty (TransverseDetector pairing distinguishedPlace placePrime x d)

/-- The one detector selected by the existential target.  The two remaining
W2 targets are indexed by this exact witness, so they cannot silently switch
detectors or demand a theorem about every possible detector. -/
noncomputable def chosenTransverseDetector
    (pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar))
    (distinguishedPlace : Place) (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode)
    (hDetector : transverse_detector_exists pairing
      distinguishedPlace placePrime x d) :
    TransverseDetector pairing distinguishedPlace placePrime x d :=
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
    (pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar))
    (distinguishedPlace : Place) (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode)
    (detector : TransverseDetector pairing distinguishedPlace placePrime x d) where
  readout : AllocatedClass K →+ ZMod 59
  unit : (ZMod 59)ˣ
  pairing_eq_gauge :
    pairing.pairAt distinguishedPlace x detector.detector =
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
  {pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
    (Place := Place) (SelmerChi := SelmerChi)
    (DOmegaSelmerChiStar := DOmegaSelmerChiStar)}
  {distinguishedPlace : Place} {placePrime : Place → ℕ}
  {x : SelmerChi} {d : LampMode}
  {detector : TransverseDetector pairing distinguishedPlace placePrime x d}

/-- Cancellation of the unit in the local comparison kills the scalar
readout of the displayed relation-(7a) word. -/
theorem scalarGauge_eq_zero_of_local_reading_eq_zero
    (comparison : GaugeComparison pair pairing distinguishedPlace
      placePrime x d detector)
    (hlocal : pairing.pairAt distinguishedPlace x detector.detector = 0) :
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
    (comparison : GaugeComparison pair pairing distinguishedPlace
      placePrime x d detector)
    (hlocal : pairing.pairAt distinguishedPlace x detector.detector = 0) :
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
    (pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar))
    (distinguishedPlace : Place) (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode)
    (hDetector : transverse_detector_exists pairing
      distinguishedPlace placePrime x d) : Prop :=
  Nonempty (GaugeComparison pair pairing distinguishedPlace
    placePrime x d
      (chosenTransverseDetector pairing distinguishedPlace
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

/-- The explicit missing localization law at the auxiliary place.  The
proved (7d) fold is a genuine input, but it may silence the local reading
only after both localized conditions and their conditional orthogonality
have been exhibited. -/
structure AuxiliaryFoldOrthogonalityGuard
    (pair : StateLinkedIdealPair hζ S hz)
    (pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar))
    (distinguishedPlace : Place) (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode)
    (detector : TransverseDetector pairing distinguishedPlace placePrime x d) where
  primalCondition : AddSubgroup SelmerChi
  dualCondition : AddSubgroup DOmegaSelmerChiStar
  primal_mem : x ∈ primalCondition
  dual_mem : detector.detector ∈ dualCondition
  orthogonal_of_sevenD : pair.ledger.VandiverSevenD 0 1 →
    ∀ x' ∈ primalCondition, ∀ y' ∈ dualCondition,
      pairing.pairAt detector.auxiliaryPlace x' y' = 0

namespace AuxiliaryFoldOrthogonalityGuard

variable
  {pair : StateLinkedIdealPair hζ S hz}
  {pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
    (Place := Place) (SelmerChi := SelmerChi)
    (DOmegaSelmerChiStar := DOmegaSelmerChiStar)}
  {distinguishedPlace : Place} {placePrime : Place → ℕ}
  {x : SelmerChi} {d : LampMode}
  {detector : TransverseDetector pairing distinguishedPlace placePrime x d}

/-- The auxiliary local reading is zero after consuming both the explicit
orthogonality interface and the actually proved statewise (7d) receipt. -/
theorem pairAt_eq_zero
    (guard : AuxiliaryFoldOrthogonalityGuard pair pairing
      distinguishedPlace placePrime x d detector) :
    pairing.pairAt detector.auxiliaryPlace x detector.detector = 0 :=
  guard.orthogonal_of_sevenD (n59BankReceipts pair).sevenD
    x guard.primal_mem detector.detector guard.dual_mem

end AuxiliaryFoldOrthogonalityGuard

/-- The complete audit object behind `bank_silences_other_places`.

The auxiliary row names the fold-specific compatibility.  Every remaining
row has a full `LocalOrthogonalityGuard`, so neither Selmer membership nor
the detector's support is mislabeled as a bank theorem.  The proved bank is
assembled when the auxiliary row is discharged; it is not duplicated as a
decorative field here. -/
structure BankSilenceAudit
    (pair : StateLinkedIdealPair hζ S hz)
    (pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar))
    (distinguishedPlace : Place) (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode)
    (detector : TransverseDetector pairing distinguishedPlace placePrime x d) where
  auxiliary : AuxiliaryFoldOrthogonalityGuard pair pairing
    distinguishedPlace placePrime x d detector
  other : ∀ v, v ≠ distinguishedPlace → v ≠ detector.auxiliaryPlace →
    TatePairing.LocalOrthogonalityGuard pairing v x detector.detector

namespace BankSilenceAudit

variable
  {pair : StateLinkedIdealPair hζ S hz}
  {pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
    (Place := Place) (SelmerChi := SelmerChi)
    (DOmegaSelmerChiStar := DOmegaSelmerChiStar)}
  {distinguishedPlace : Place} {placePrime : Place → ℕ}
  {x : SelmerChi} {d : LampMode}
  {detector : TransverseDetector pairing distinguishedPlace placePrime x d}

/-- Audit row for the lamp-selected auxiliary place. -/
theorem auxiliary_reading_eq_zero
    (audit : BankSilenceAudit pair pairing distinguishedPlace
      placePrime x d detector) :
    pairing.pairAt detector.auxiliaryPlace x detector.detector = 0 :=
  audit.auxiliary.pairAt_eq_zero

/-- Audit row for an arbitrary place outside the distinguished/auxiliary
pair, consuming the explicit local-condition orthogonality guard. -/
theorem other_reading_eq_zero
    (audit : BankSilenceAudit pair pairing distinguishedPlace
      placePrime x d detector)
    (v : Place) (hv : v ≠ distinguishedPlace)
    (haux : v ≠ detector.auxiliaryPlace) :
    pairing.pairAt v x detector.detector = 0 :=
  (audit.other v hv haux).pairAt_eq_zero

/-- The place-by-place audit silences every column other than the
distinguished one, including the auxiliary column as a separate case. -/
theorem away_reading_eq_zero
    (audit : BankSilenceAudit pair pairing distinguishedPlace
      placePrime x d detector)
    (v : Place) (hv : v ≠ distinguishedPlace) :
    pairing.pairAt v x detector.detector = 0 := by
  by_cases haux : v = detector.auxiliaryPlace
  · subst v
    exact audit.auxiliary_reading_eq_zero
  · exact audit.other_reading_eq_zero v hv haux

end BankSilenceAudit

/-- **INTERFACE — W2.3.** A place-by-place audit for the same transverse
detector.  Its bank assembly is already proved, while its auxiliary
localization compatibility and all local orthogonality rows remain explicit
interfaces. -/
def bank_silences_other_places
    (pair : StateLinkedIdealPair hζ S hz)
    (pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar))
    (distinguishedPlace : Place) (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode)
    (hDetector : transverse_detector_exists pairing
      distinguishedPlace placePrime x d) : Prop :=
  Nonempty (BankSilenceAudit pair pairing distinguishedPlace
    placePrime x d
      (chosenTransverseDetector pairing distinguishedPlace
        placePrime x d hDetector))

/-! ## W3: the compiled conditional implication -/

namespace StateLinkedIdealPair

/-- **PROVEN conditional master theorem.** The W1 pairing/adjoint interface
and reciprocity law, together with exactly the three named W2 arithmetic
hypotheses, force the selected difference gauge to vanish and hence prove
relation (7a) through the existing exact gauge theorem.

This is deliberately not an unconditional `vandiverSevenA` declaration.
Its mod-59 depth limitation is recorded below as the named
`mu_59_to_the_n_risk`; the theorem does not claim that first-layer pairings
detect a class living deeper in the 59-power tower. -/
theorem vandiverSevenA_of_tate_bridge
    (pair : StateLinkedIdealPair hζ S hz)
    (pairing : LocalPairing (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar))
    (reciprocity : TatePairing.GlobalReciprocityLaw pairing)
    (distinguishedPlace : Place) (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode)
    (hDetector : transverse_detector_exists pairing
      distinguishedPlace placePrime x d)
    (hGauge : gauge_eq_local_tate_pairing pair pairing
      distinguishedPlace placePrime x d hDetector)
    (hBank : bank_silences_other_places pair pairing
      distinguishedPlace placePrime x d hDetector) :
    pair.ledger.VandiverSevenA 0 1 := by
  let detector := chosenTransverseDetector pairing distinguishedPlace
    placePrime x d hDetector
  change Nonempty (GaugeComparison pair pairing distinguishedPlace
    placePrime x d detector) at hGauge
  change Nonempty (BankSilenceAudit pair pairing distinguishedPlace
    placePrime x d detector) at hBank
  rcases hGauge with ⟨comparison⟩
  rcases hBank with ⟨audit⟩
  have hother : ∀ v, v ≠ distinguishedPlace →
      pairing.pairAt v x detector.detector = 0 := by
    intro v hv
    exact audit.away_reading_eq_zero v hv
  have hlocal :
      pairing.pairAt distinguishedPlace x detector.detector = 0 :=
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
