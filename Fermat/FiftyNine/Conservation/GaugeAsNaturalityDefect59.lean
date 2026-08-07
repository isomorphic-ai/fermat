/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The conductor-59 gauge is not a PowerRoot naturality defect

There are two different diagrams in play.

* A PowerRoot localization face starts with one global divisible class.  Its
  two routes are `obstruction_local (localize x)` and
  `localize (obstruction_global x)`.  The generic naturality theorem may make
  this square commute, and a principal local class shadow may even make both
  sides trivial.
* The selected conductor-59 gauge starts with the class shadows of two
  independently allocated ideal roots.  `TateBridge.GaugeComparison` reads
  their difference through a wild, reflected-dual Tate pairing.  It does not
  turn those two roots into the two composites of one PowerRoot input.

The four-constructor `GaugeNaturalityOutcome` makes every possible result of
the decisive test typed.  `gaugeNaturalityOutcome59` selects the fourth:
the actual wild route has different provenance from the same-input
PowerRoot localization square.  This is deliberately a statement about the
constructed routes, not a claim that values in unrelated carriers can never
coincide accidentally.

The final section retains `r0 + 58*r1 = (r0-r1) + 59*r1` on a formal
integral lift.  Its `59*r1` term is recorded only as a candidate
Bockstein/PowerRoot receipt.  No arithmetic depth consequence is asserted.
-/
import Fermat.Conservation.Credit.DepthCertificate
import Fermat.Conservation.Interaction
import Fermat.Conservation.PowerRootNaturality
import Fermat.FiftyNine.Conservation.TateBridge

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.KummerDrain
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.PowerRootNaturality
open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.StateFactorPair
open PowerRoot

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

universe uP uQ uA uB uC uD
  uSelmer uDual uDelta uLamp uClass uGlobal uLocal uCompare

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {zeta : K} {hzeta : IsPrimitiveRoot zeta 59}
  {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}

/-! ## The two readings actually selected by the allocated Fermat pair -/

/-- `r0` is the class shadow of the first independently allocated ideal
root.  It is a value, not a renamed localization composite. -/
def r0 (pair : StateLinkedIdealPair hzeta S hz) : AllocatedClass K :=
  pair.ledger.rootClass 0

/-- `r1` is the class shadow of the second independently allocated ideal
root.  Its input allocation is distinct from the input allocation of `r0`. -/
def r1 (pair : StateLinkedIdealPair hzeta S hz) : AllocatedClass K :=
  pair.ledger.rootClass 1

/-- The selected conductor-59 word before using its first-layer torsion
receipt.  No vanishing is included in this definition. -/
def selectedGauge (pair : StateLinkedIdealPair hzeta S hz) :
    AllocatedClass K :=
  r0 pair + 58 • r1 pair

/-- The implemented selected readings, including the ledger input which
produced each value.  These source indices are part of the construction and
are not reconstructed from an accidental equality after a scalar readout. -/
structure SelectedAllocatedReadings
    (pair : StateLinkedIdealPair hzeta S hz) where
  r0Source : Fin 2
  r1Source : Fin 2
  r0Value : AllocatedClass K
  r1Value : AllocatedClass K
  r0Value_eq_rootClass : r0Value = pair.ledger.rootClass r0Source
  r1Value_eq_rootClass : r1Value = pair.ledger.rootClass r1Source

/-- The concrete source-bearing record behind the selected `r0` and `r1`.
The first value comes from allocation `0`; the second comes from allocation
`1`. -/
def selectedAllocatedReadings
    (pair : StateLinkedIdealPair hzeta S hz) :
    SelectedAllocatedReadings pair where
  r0Source := 0
  r1Source := 1
  r0Value := r0 pair
  r1Value := r1 pair
  r0Value_eq_rootClass := rfl
  r1Value_eq_rootClass := rfl

/-- The two selected readings retain distinct allocated source slots.  This
is a statement about the construction record, not about inequality of their
class-group values. -/
theorem selectedAllocatedReadings_sources_ne
    (pair : StateLinkedIdealPair hzeta S hz) :
    (selectedAllocatedReadings pair).r0Source ≠
      (selectedAllocatedReadings pair).r1Source := by
  norm_num [selectedAllocatedReadings]

/-- The two candidate sides of a same-input localization square. -/
inductive PowerRootLocalizationSide
  | localObstructionAfterLocalize
  | localizeAfterGlobalObstruction
deriving DecidableEq, Repr

/-- Provenance of a reading used in the decisive test.

The constructor records how a reading was built.  It does not claim that
values with different provenance are unequal after an arbitrary readout. -/
inductive ReadingProvenance
  | sameInputPowerRoot (side : PowerRootLocalizationSide)
  | allocatedRootClass (index : Fin 2)
  | wildReflectedTate
deriving DecidableEq, Repr

/-! ## The genuine same-input PowerRoot localization face -/

section GenericPowerRootLocalization

variable {P : Type uP} {Q : Type uQ}
  {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [CommGroup A] [CommGroup B] [CommGroup C] [CommGroup D]
  {globalArrow : A →* B} {localArrow : C →* D}
  {n : ℕ} [Fact (0 < n)]

/-- Candidate `r0(x)`: take the local obstruction after localizing the one
global divisible class `x`. -/
def powerRootR0Candidate
    (localization : LocalizationInterface globalArrow localArrow)
    (localGeometry : Factorization D Q)
    (input : divisibleClasses globalArrow n) :
    D ⧸ localArrow.range :=
  localization.localObstructionAfterLocalization localGeometry input

/-- Candidate `r1(x)`: take the global obstruction of that same `x`, then
localize its cokernel class. -/
def powerRootR1Candidate
    (localization : LocalizationInterface globalArrow localArrow)
    (globalGeometry : Factorization B P)
    (input : divisibleClasses globalArrow n) :
    D ⧸ localArrow.range :=
  localization.localizationAfterGlobalObstruction globalGeometry input

/-- The multiplicative naturality defect of the genuine same-input square. -/
def powerRootLocalizationDefect
    (localization : LocalizationInterface globalArrow localArrow)
    (globalGeometry : Factorization B P)
    (localGeometry : Factorization D Q)
    (input : divisibleClasses globalArrow n) :
    D ⧸ localArrow.range :=
  powerRootR0Candidate localization localGeometry input /
    powerRootR1Candidate localization globalGeometry input

/-- Typed receipt for the generic PowerRoot localization face.  Both routes
carry the same input in the same cokernel, and W2 naturality makes their
defect trivial whenever the two factorized carriers have really been
supplied. -/
structure SameInputPowerRootLocalizationFace
    (localization : LocalizationInterface globalArrow localArrow)
    (globalGeometry : Factorization B P)
    (localGeometry : Factorization D Q)
    (input : divisibleClasses globalArrow n) : Prop where
  routes_commute :
    powerRootR0Candidate localization localGeometry input =
      powerRootR1Candidate localization globalGeometry input
  defect_eq_one :
    powerRootLocalizationDefect localization globalGeometry localGeometry
      input = 1

/-- The W2 obstruction-square theorem produces the genuine same-input face.
This does not identify either route with an allocated conductor-59 root. -/
def sameInputPowerRootLocalizationFace
    (localization : LocalizationInterface globalArrow localArrow)
    (globalGeometry : Factorization B P)
    (localGeometry : Factorization D Q)
    (input : divisibleClasses globalArrow n) :
    SameInputPowerRootLocalizationFace localization globalGeometry
      localGeometry input where
  routes_commute :=
    localization.obstruction_square globalGeometry localGeometry input
  defect_eq_one := by
    unfold powerRootLocalizationDefect powerRootR0Candidate
      powerRootR1Candidate
    rw [localization.obstruction_square globalGeometry localGeometry input]
    simp

/-- Optional local trivialization of the generic PowerRoot class shadow.
This is a named condition, not an assertion that the missing arithmetic
local carrier exists.  It is compatible with, but logically stronger than,
the commuting-square receipt above. -/
structure LocalPowerRootClassShadowTrivialization
    (localization : LocalizationInterface globalArrow localArrow)
    (globalGeometry : Factorization B P)
    (localGeometry : Factorization D Q)
    (input : divisibleClasses globalArrow n) : Prop where
  local_after_localize_eq_one :
    powerRootR0Candidate localization localGeometry input = 1
  localize_after_global_eq_one :
    powerRootR1Candidate localization globalGeometry input = 1

end GenericPowerRootLocalization

/-- Construction provenance of the selected `r0`. -/
def r0Provenance : ReadingProvenance :=
  .allocatedRootClass 0

/-- Construction provenance of the selected `r1`. -/
def r1Provenance : ReadingProvenance :=
  .allocatedRootClass 1

/-- Construction provenance of the scalar comparison in
`TateBridge.GaugeComparison`. -/
def gaugeComparisonProvenance : ReadingProvenance :=
  .wildReflectedTate

/-- The attempted identification which would make the selected gauge the
defect of a single PowerRoot localization square.

It asks the two implemented selected readings to share a source and asks for
their route provenance to be the two ordered routes of one global input.
Value equalities are intentionally not enough: factorization is a statement
about the arrows and selected source which produced the values. -/
structure SameInputPowerRootIdentification
    (pair : StateLinkedIdealPair hzeta S hz) : Prop where
  shared_selected_input :
    (selectedAllocatedReadings pair).r0Source =
      (selectedAllocatedReadings pair).r1Source
  r0_route :
    r0Provenance =
      .sameInputPowerRoot .localObstructionAfterLocalize
  r1_route :
    r1Provenance =
      .sameInputPowerRoot .localizeAfterGlobalObstruction

theorem noSameInputPowerRootIdentification
    (pair : StateLinkedIdealPair hzeta S hz) :
    ¬ SameInputPowerRootIdentification pair := by
  intro identification
  have hsources : (0 : Fin 2) = 1 := identification.shared_selected_input
  norm_num at hsources

/-! ## The four typed outcomes -/

/-- Outcome 1 data: the selected readings really are the two routes of one
PowerRoot input, so direct generic naturality applies. -/
structure DirectPowerRootNaturalityOutcome
    (pair : StateLinkedIdealPair hzeta S hz) : Prop where
  identification : SameInputPowerRootIdentification pair

/-- A finitely supported family of local defects whose total is killed by a
reciprocity law.  This is the additive shape of
`TatePairing.GlobalReciprocityLaw.sum_eq_zero`; it does not manufacture such
a law for the allocated-root gauge. -/
structure GlobalReciprocityTwoCell (Place : Type)
    (Class : Type uClass) [AddCommGroup Class] where
  localDefect : Place →₀ Class
  sum_eq_zero : localDefect.sum (fun _ value => value) = 0

/-- Outcome 2 data: a zero-reflecting scalar readout of the selected
difference is the sum of placewise defects, and the supplied
global-reciprocity 2-cell closes precisely that sum. -/
structure ReciprocityNaturalityOutcome
    (pair : StateLinkedIdealPair hzeta S hz) where
  Place : Type
  twoCell : GlobalReciprocityTwoCell Place (ZMod 59)
  readout : AllocatedClass K →+ ZMod 59
  selected_eq_sum :
    readout (r0 pair - r1 pair) =
      twoCell.localDefect.sum (fun _ value => value)
  reflects_selected_zero :
    readout (r0 pair - r1 pair) = 0 → r0 pair - r1 pair = 0

/-- Named missing carrier for outcome 3.  The two insertion maps are the
required reflected-character/Tate-twist comparison; no such maps are
silently supplied by merely naming their source and target types. -/
structure ReflectedDualLocalizationCarrier where
  globalClassCarrier : Type uGlobal
  localChiStarTateTwistedCarrier : Type uLocal
  comparisonCarrier : Type uCompare
  insertGlobal : globalClassCarrier → comparisonCarrier
  insertReflectedTate :
    localChiStarTateTwistedCarrier → comparisonCarrier

/-- Outcome 3 data: comparison becomes meaningful only after inserting the
named reflected-dual localization carrier. -/
structure ReflectedDualCarrierOutcome where
  carrier : ReflectedDualLocalizationCarrier

/-- Outcome 4 data: the selected values come from two allocations and the
comparison is wild Tate data, so their constructed route does not factor as
the two sides of one PowerRoot localization input.

The scope is the implemented, source-preserving route: its selected inputs
are the distinct ledger indices `0` and `1`.  This record does not assert
universal nonexistence of some unrelated square, nor inequality after an
arbitrary scalar readout.

The final two fields separate the wild comparison from both generic route
constructors.  This outcome does not deny the generic obstruction square or
its possible local trivialization. -/
structure DifferentObstructionOutcome
    (pair : StateLinkedIdealPair hzeta S hz) : Prop where
  selectedR0Value : r0 pair = pair.ledger.rootClass 0
  selectedR1Value : r1 pair = pair.ledger.rootClass 1
  selectedR0Source : (selectedAllocatedReadings pair).r0Source = 0
  selectedR1Source : (selectedAllocatedReadings pair).r1Source = 1
  selectedSources_ne :
    (selectedAllocatedReadings pair).r0Source ≠
      (selectedAllocatedReadings pair).r1Source
  selectedR0Provenance : r0Provenance = .allocatedRootClass 0
  selectedR1Provenance : r1Provenance = .allocatedRootClass 1
  wildComparison : gaugeComparisonProvenance = .wildReflectedTate
  notSameInputPowerRoot : ¬ SameInputPowerRootIdentification pair
  wild_ne_local_after_localize :
    gaugeComparisonProvenance ≠
      .sameInputPowerRoot .localObstructionAfterLocalize
  wild_ne_localize_after_global :
    gaugeComparisonProvenance ≠
      .sameInputPowerRoot .localizeAfterGlobalObstruction

/-- Exactly the four typed results of the decisive naturality test.  A term
of this inductive type selects one constructor; there is no Boolean fallback
or fifth untyped case. -/
inductive GaugeNaturalityOutcome
    (pair : StateLinkedIdealPair hzeta S hz)
  | outcomeOne (result : DirectPowerRootNaturalityOutcome pair)
  | outcomeTwo (result : ReciprocityNaturalityOutcome pair)
  | outcomeThree (result : ReflectedDualCarrierOutcome)
  | outcomeFour (result : DifferentObstructionOutcome pair)

/-- **DECISIVE TEST — outcome 4.**  The conductor-59 gauge/Tate route is not
the naturality defect of the same-input PowerRoot localization square.

This classification neither disputes generic PowerRoot naturality nor says
that a local class shadow must be nonzero.  It says that the actual selected
route has two distinct allocated source indices and different construction
provenance, so it is not the two ordered images of one selected PowerRoot
input.  It makes no universal claim about accidental scalar equalities.  The
wild arithmetic comparison therefore remains genuinely necessary. -/
def gaugeNaturalityOutcome59
    (pair : StateLinkedIdealPair hzeta S hz) :
    GaugeNaturalityOutcome pair :=
  .outcomeFour {
    selectedR0Value := rfl
    selectedR1Value := rfl
    selectedR0Source := rfl
    selectedR1Source := rfl
    selectedSources_ne := selectedAllocatedReadings_sources_ne pair
    selectedR0Provenance := rfl
    selectedR1Provenance := rfl
    wildComparison := rfl
    notSameInputPowerRoot := noSameInputPowerRootIdentification pair
    wild_ne_local_after_localize := by intro h; cases h
    wild_ne_localize_after_global := by intro h; cases h }

/-- On the selected 59-torsion layer, the coefficient `58` is `-1`, so the
open gauge is exactly the difference reading.  No vanishing is asserted. -/
theorem selectedGauge_eq_difference
    (pair : StateLinkedIdealPair hzeta S hz) :
    selectedGauge pair = r0 pair - r1 pair :=
  (Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.differenceGauge_reading
    pair).symm

/-! ## The actual `GaugeComparison` is on the wild route -/

variable {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt 59) Delta}
  {Place : Type} {SelmerChi : Type uSelmer}
  {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra 59 Delta) DOmegaSelmerChiStar]
  [Module (Polynomial (ZMod 59)) DOmegaSelmerChiStar]
  {LampMode : Type uLamp} [AddCommGroup LampMode]
  [Module (Polynomial (ZMod 59)) LampMode]
  {pair : StateLinkedIdealPair hzeta S hz}
  {distinguishedPlace : Place}
  {wild : TateBridge.WildLocalInterface
    (Delta := Delta) (omega := omega) (chi := chi)
    (Place := Place) (SelmerChi := SelmerChi)
    (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace}
  {placePrime : Place → ℕ}
  {x : SelmerChi} {d : LampMode}
  {detector : TateBridge.TransverseDetector distinguishedPlace wild
    placePrime x d}

/-- The exact adapter from the repository's global reciprocity law to the
typed 2-cell used by outcome 2.  It retains the complete finitely supported
family of scalar Tate readings.  By itself it does not identify that family
with the two allocated-root readings. -/
def globalReciprocityTwoCellOfLaw
    (reciprocity : TatePairing.GlobalReciprocityLaw
      wild.toPlaceIndexedLocalPairing) :
    GlobalReciprocityTwoCell Place (ZMod 59) where
  localDefect := wild.toPlaceIndexedLocalPairing.readings x detector.detector
  sum_eq_zero := reciprocity.sum_eq_zero x detector.detector

/-- The actual data path through a concrete `TateBridge.GaugeComparison`.
It retains both the local reflected-dual Tate reading and the explicit
readout of the selected allocated-root gauge. -/
structure GaugeComparisonRoute
    (comparison : TateBridge.GaugeComparison pair distinguishedPlace wild
      placePrime x d detector) where
  localTateReading : ZMod 59
  selectedClassReadout : ZMod 59
  comparisonLaw : localTateReading = selectedClassReadout
  provenance : ReadingProvenance
  wildProvenance : provenance = .wildReflectedTate

/-- A concrete gauge comparison produces the wild route record directly
from its pairing/readout law. -/
def gaugeComparisonRoute
    (comparison : TateBridge.GaugeComparison pair distinguishedPlace wild
      placePrime x d detector) : GaugeComparisonRoute comparison where
  localTateReading :=
    wild.toPlaceIndexedLocalPairing.pairAt
      distinguishedPlace x detector.detector
  selectedClassReadout :=
    (comparison.unit : ZMod 59) * comparison.readout (selectedGauge pair)
  comparisonLaw := by
    simpa only [selectedGauge, r0, r1] using comparison.pairing_eq_gauge
  provenance := .wildReflectedTate
  wildProvenance := rfl

/-- Reading a concrete `TateBridge.GaugeComparison` retains its actual wild
route tag.  The comparison's scalar is obtained from a reflected-dual local
pairing and an explicit class readout; it is not a PowerRoot obstruction
map. -/
def routeOfGaugeComparison
    (comparison : TateBridge.GaugeComparison pair distinguishedPlace wild
      placePrime x d detector) : ReadingProvenance :=
  (gaugeComparisonRoute comparison).provenance

/-- Mechanical route guard for the concrete comparison: it cannot be the
`obstruction_local (localize x)` constructor of a same-input PowerRoot face. -/
def gaugeComparisonNotLocalAfterLocalize
    (comparison : TateBridge.GaugeComparison pair distinguishedPlace wild
      placePrime x d detector) :
    routeOfGaugeComparison comparison ≠
      .sameInputPowerRoot .localObstructionAfterLocalize := by
  intro h
  cases h

/-- Mechanical route guard for the concrete comparison: it cannot be the
`localize (obstruction_global x)` constructor of a same-input PowerRoot
face. -/
def gaugeComparisonNotLocalizeAfterGlobal
    (comparison : TateBridge.GaugeComparison pair distinguishedPlace wild
      placePrime x d detector) :
    routeOfGaugeComparison comparison ≠
      .sameInputPowerRoot .localizeAfterGlobalObstruction := by
  intro h
  cases h

/-! ## The retained depth receipt is an observation -/

/-- Formal integral coordinates lifting the two selected class readings.
The map to the first class layer is defined below; retaining these
coordinates prevents the `59*r1` correction from disappearing too early. -/
abbrev IntegralGaugeLift := ℤ × ℤ

/-- Formal integral lift of `r0`. -/
def integralR0 : IntegralGaugeLift := (1, 0)

/-- Formal integral lift of `r1`. -/
def integralR1 : IntegralGaugeLift := (0, 1)

/-- The correction retained beyond the first 59-torsion reading. -/
def bocksteinPowerRootReceipt : IntegralGaugeLift :=
  (59 : ℤ) • integralR1

/-- The two occurrences of the numeral two remain in unrelated carriers:

* `Credit.RealFlow.DepthTwoCertificate` is Bernoulli depth data;
* `Interaction.critical_period_two` is the critical-gain orbit law.

There is no transport map between those carriers in this observation. -/
inductive TwoTwosCorrespondenceStatus
  | openUntilDepthToInteractionTransport
deriving DecidableEq, Repr

/-- **OBSERVATION — candidate Bockstein/PowerRoot receipt.**

The record retains the exact integral decomposition and its reduction to the
selected class layer.  `formal_receipt_ne_zero` concerns only the free
integral coordinates; `reduction_receipt_eq_zero` says that the known
59-torsion projection discards that correction.  Neither field asserts a
nonzero arithmetic Bockstein, a depth theorem, or the open two-2s
correspondence. -/
structure BocksteinPowerRootReceiptObservation
    (pair : StateLinkedIdealPair hzeta S hz) where
  reduction : IntegralGaugeLift →+ AllocatedClass K
  reduction_r0 : reduction integralR0 = r0 pair
  reduction_r1 : reduction integralR1 = r1 pair
  exact_integral_decomposition :
    integralR0 + (58 : ℤ) • integralR1 =
      (integralR0 - integralR1) + bocksteinPowerRootReceipt
  receipt_is_59_times_r1 :
    bocksteinPowerRootReceipt = (59 : ℤ) • integralR1
  formal_receipt_ne_zero : bocksteinPowerRootReceipt ≠ 0
  reduction_receipt_eq_zero :
    reduction bocksteinPowerRootReceipt = 0
  first_layer_gauge_eq_difference :
    selectedGauge pair = r0 pair - r1 pair
  firstLayerDepthRisk : TateBridge.Mu59ToTheNRisk
  twoTwosCorrespondence : TwoTwosCorrespondenceStatus

private def integralReduction
    (pair : StateLinkedIdealPair hzeta S hz) :
    IntegralGaugeLift →+ AllocatedClass K where
  toFun coefficients :=
    coefficients.1 • r0 pair + coefficients.2 • r1 pair
  map_zero' := by simp
  map_add' left right := by
    simp only [Prod.fst_add, Prod.snd_add, add_zsmul]
    abel

/-- The selected pair's named depth observation.  The only arithmetic input
is the already-proved 59-torsion receipt for the second allocated root. -/
def bocksteinPowerRootReceiptObservation
    (pair : StateLinkedIdealPair hzeta S hz) :
    BocksteinPowerRootReceiptObservation pair where
  reduction := integralReduction pair
  reduction_r0 := by simp [integralReduction, integralR0, r0]
  reduction_r1 := by simp [integralReduction, integralR1, r1]
  exact_integral_decomposition := by
    norm_num [integralR0, integralR1, bocksteinPowerRootReceipt]
  receipt_is_59_times_r1 := rfl
  formal_receipt_ne_zero := by
    norm_num [bocksteinPowerRootReceipt, integralR1]
  reduction_receipt_eq_zero := by
    rw [bocksteinPowerRootReceipt, map_zsmul]
    have hreduction : integralReduction pair integralR1 = r1 pair := by
      simp [integralReduction, integralR1, r1]
    rw [hreduction, ofNat_zsmul]
    exact pair.ledger.rootClass_torsion 1
  first_layer_gauge_eq_difference := by
    exact selectedGauge_eq_difference pair
  firstLayerDepthRisk := TateBridge.mu_59_to_the_n_risk
  twoTwosCorrespondence :=
    .openUntilDepthToInteractionTransport

end Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59
