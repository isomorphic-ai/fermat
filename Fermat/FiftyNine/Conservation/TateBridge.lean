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

The detector proposition below is the pre-Stage-2 abstract interface used by
the conditional implication.  It is not yet an explicit Poitou--Tate witness:
the generic dual carrier has no global Kummer representative, and this
single-wild-column pairing forces its auxiliary reading to zero.  The
separate `DetectorWitness827` audit states the honest q-relaxed target and
proves why the current empty-support seated instance cannot inhabit it.

The comparison with the selected gauge and global reciprocity remain explicit
interfaces.  No unconditional relation (7a), endpoint, or transformer is
asserted here.
-/
import Fermat.Conservation.TamePlacePairing
import Fermat.Conservation.SteeringFiber
import Fermat.FiftyNine.Conservation.CommonActionStage
import Fermat.FiftyNine.Conservation.Instance
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.TateBridge

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.TatePairing
open Fermat.Conservation.TamePlacePairing
open Fermat.Conservation.TransverseAnnihilator
open Fermat.Conservation.SteeringFiber
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

/-! ## The cohomological Stokes detector -/

/-- The remaining Fermat potential carrier exposed by the existing pairing
surface.  In the conditional master theorem the selected `x : H_FLT` is
seated against the class-group difference gauge by `GaugeComparison`; this
abbreviation does not manufacture a map from the Selmer carrier to
`AllocatedClass K`. -/
abbrev H_FLT (M : Type uSelmer) := M

/-- The honest additive detector dual exposed by the reflected Selmer leg.
No identification with a larger algebraic or Pontryagin dual is asserted. -/
abbrev WildDetectorDual (D : Type uDual) [AddCommGroup D] :=
  D →+ ZMod 59

/-- The distinguished conductor-59 pairing, curried as the complete family
of wild detector readings. -/
def pair_59
    {distinguishedPlace : Place}
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace) :
    H_FLT SelmerChi →+ WildDetectorDual DOmegaSelmerChiStar :=
  wild.reading

/-- The Stokes detector on the remaining difference-mode potential. -/
def Lambda
    {distinguishedPlace : Place}
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace) :
    H_FLT SelmerChi →+ WildDetectorDual DOmegaSelmerChiStar :=
  pair_59 wild

/-! ## The scalar question quotient -/

/-- The relation-(7a) information visible to a supplied scalar gauge.  The
present cone does not yet construct such a gauge on `H_FLT`; keeping it as
an argument makes that seating boundary explicit. -/
abbrev Q_7a [Module (ZMod 59) SelmerChi]
    (gauge : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59) :=
  ScalarQuestionQuotient gauge

/-- Every scalar relation-(7a) gauge has zero vacuum offset. -/
@[simp]
theorem sevenAGauge_vacuum [Module (ZMod 59) SelmerChi]
    (gauge : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59) :
    gauge 0 = 0 :=
  map_zero gauge

/-- **ULAM DETECTOR BUDGET.**  The claim-relevant quotient has dimension at
most one even when the ambient Selmer carrier has arbitrary dimension. -/
theorem Q_7a_finrank_le_one [Module (ZMod 59) SelmerChi]
    (gauge : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59) :
    Module.finrank (ZMod 59) (Q_7a gauge) ≤ 1 :=
  scalarQuestionQuotient_finrank_le_one gauge

/-- A functional on `H_FLT`, descended through the gauge quotient under the
exact required kernel inclusion.  The current cone does not yet identify
W4's fixed readout with such a functional on `H_FLT`. -/
noncomputable def descendedFunctionalOnQ_7a [Module (ZMod 59) SelmerChi]
    (gauge : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59)
    (lambda : Module.Dual (ZMod 59) (H_FLT SelmerChi))
    (descends : gauge.ker ≤ lambda.ker) :
    Module.Dual (ZMod 59) (Q_7a gauge) :=
  scalarQuestionDual gauge lambda descends

/-- Pullback of the descended functional is the original reading. -/
theorem descendedFunctionalOnQ_7a_pullback [Module (ZMod 59) SelmerChi]
    (gauge : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59)
    (lambda : Module.Dual (ZMod 59) (H_FLT SelmerChi))
    (descends : gauge.ker ≤ lambda.ker) (x : H_FLT SelmerChi) :
    descendedFunctionalOnQ_7a gauge lambda descends (gauge.ker.mkQ x) =
      lambda x :=
  scalarQuestionDual_pullback gauge lambda descends x

/-- The descended quotient readout does not depend on the chosen
representative. -/
theorem descendedFunctionalOnQ_7a_preimage_independent
    [Module (ZMod 59) SelmerChi]
    (gauge : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59)
    (lambda : Module.Dual (ZMod 59) (H_FLT SelmerChi))
    (descends : gauge.ker ≤ lambda.ker) {x y : H_FLT SelmerChi}
    (hxy : gauge.ker.mkQ x = gauge.ker.mkQ y) :
    lambda x = lambda y :=
  scalarQuestionDual_preimage_independent gauge lambda descends hxy

omit [Module (Polynomial (ZMod 59)) DOmegaSelmerChiStar] in
/-- Evaluation of `Lambda` is exactly the existing pairing at the
distinguished place above 59. -/
@[simp] theorem Lambda_apply
    {distinguishedPlace : Place}
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    (x : H_FLT SelmerChi) (y : DOmegaSelmerChiStar) :
    Lambda wild x y =
      wild.toPlaceIndexedLocalPairing.pairAt distinguishedPlace x y :=
  (wild.pairAt_distinguished x y).symm

omit [Module (Polynomial (ZMod 59)) DOmegaSelmerChiStar] in
/-- **PROVEN arithmetic Stokes theorem.**  The complete pairing was built
with only its wild column: every tame/away boundary reading is zero.  Global
reciprocity therefore says that the wild face carries zero net flux, i.e.
`Lambda x = 0` as a functional on every reflected-dual detector. -/
theorem Lambda_apply_eq_zero_of_reciprocity
    {distinguishedPlace : Place}
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    (reciprocity : TatePairing.GlobalReciprocityLaw
      wild.toPlaceIndexedLocalPairing)
    (x : H_FLT SelmerChi) :
    Lambda wild x = 0 := by
  ext y
  rw [Lambda_apply]
  exact reciprocity.pairAt_eq_zero_of_other_places
    distinguishedPlace x y
      (fun v hv => wild.pairAt_eq_zero_of_ne hv x y)

/-- **RETAINED GLOBAL SUFFICIENT INTERFACE.**  The wild detector family
separates the entire remaining potential exactly when its kernel is zero.
This is sufficient for relation (7a), but it is not necessary: the weaker
query-level condition `wild_detector_faithful_on_Q_7a` below only asks that
zero wild reading imply zero gauge.  No value of either interface is
supplied here.

When `H_FLT` has finrank one, the theorem
`wild_detector_faithful_of_finrank_one` below reduces this family-level
condition to one transverse detector with a nonzero reading. -/
def wild_detector_faithful
    {distinguishedPlace : Place}
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace) : Prop :=
  (Lambda wild).ker = ⊥

/-- **QUERY-LEVEL FRONTIER.**  The wild detector is faithful on the
relation-(7a) quotient exactly in the only direction consumed downstream:
a zero wild functional forces the scalar gauge to vanish.  This retains the
whole ambient kernel of the gauge. -/
def wild_detector_faithful_on_Q_7a
    {distinguishedPlace : Place}
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    [Module (ZMod 59) SelmerChi]
    (gauge : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59) : Prop :=
  ∀ x : H_FLT SelmerChi, Lambda wild x = 0 → gauge x = 0

omit [Module (Polynomial (ZMod 59)) DOmegaSelmerChiStar] in
/-- Faithfulness consumes a zero detector reading and kills the underlying
potential.  It does not by itself identify that Selmer potential with the
class-group relation-(7a) gauge. -/
theorem eq_zero_of_wild_detector_faithful
    {distinguishedPlace : Place}
    {wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace}
    (faithful : wild_detector_faithful wild)
    {x : H_FLT SelmerChi} (hx : Lambda wild x = 0) :
    x = 0 := by
  have hinjective : Function.Injective (Lambda wild) :=
    (AddMonoidHom.ker_eq_bot_iff (Lambda wild)).mp faithful
  apply hinjective
  simpa using hx

omit [Module (Polynomial (ZMod 59)) DOmegaSelmerChiStar] in
/-- Global detector faithfulness is a retained sufficient conversion into
query-level faithfulness; the converse is neither required nor asserted. -/
theorem wild_detector_faithful_on_Q_7a_of_global
    {distinguishedPlace : Place}
    {wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace}
    [Module (ZMod 59) SelmerChi]
    {gauge : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59}
    (faithful : wild_detector_faithful wild) :
    wild_detector_faithful_on_Q_7a wild gauge := by
  intro x hx
  have hx0 : x = 0 := eq_zero_of_wild_detector_faithful faithful hx
  subst x
  exact map_zero gauge

omit [Module (Polynomial (ZMod 59)) DOmegaSelmerChiStar] in
/-- Quotient-form sibling of `eq_zero_of_wild_detector_faithful`: only the
claim-relevant scalar gauge is killed; the ambient potential is retained. -/
theorem gauge_eq_zero_of_wild_detector_faithful_on_Q_7a
    {distinguishedPlace : Place}
    {wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace}
    [Module (ZMod 59) SelmerChi]
    {gauge : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59}
    (faithful : wild_detector_faithful_on_Q_7a wild gauge)
    {x : H_FLT SelmerChi} (hx : Lambda wild x = 0) :
    gauge x = 0 :=
  faithful x hx

omit [Module (Polynomial (ZMod 59)) DOmegaSelmerChiStar] in
/-- Stokes vanishing followed by the retained global faithfulness condition
kills the selected potential.  This is an older sufficient route, not the
query-level frontier.  The separate `GaugeComparison` remains necessary
before the result can be read as a class-group difference-gauge statement. -/
theorem potential_eq_zero_of_stokes_and_faithful
    {distinguishedPlace : Place}
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    (reciprocity : TatePairing.GlobalReciprocityLaw
      wild.toPlaceIndexedLocalPairing)
    (faithful : wild_detector_faithful wild)
    (x : H_FLT SelmerChi) :
    x = 0 :=
  eq_zero_of_wild_detector_faithful faithful
    (Lambda_apply_eq_zero_of_reciprocity wild reciprocity x)

omit [Module (Polynomial (ZMod 59)) DOmegaSelmerChiStar] in
/-- Quotient-form sibling of `potential_eq_zero_of_stokes_and_faithful`:
reciprocity kills the relation-(7a) question without erasing the gauge
kernel or demanding global injectivity of the detector family. -/
theorem gauge_eq_zero_of_stokes_and_faithful_on_Q_7a
    {distinguishedPlace : Place}
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    (reciprocity : TatePairing.GlobalReciprocityLaw
      wild.toPlaceIndexedLocalPairing)
    [Module (ZMod 59) SelmerChi]
    (gauge : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59)
    (faithful : wild_detector_faithful_on_Q_7a wild gauge)
    (x : H_FLT SelmerChi) :
    gauge x = 0 :=
  gauge_eq_zero_of_wild_detector_faithful_on_Q_7a faithful
    (Lambda_apply_eq_zero_of_reciprocity wild reciprocity x)

omit [Module (Polynomial (ZMod 59)) DOmegaSelmerChiStar] in
/-- In a one-dimensional *ambient* remaining potential, one nonzero
transverse reading makes the complete wild detector family faithful.  This
retained sufficient theorem assumes `finrank H_FLT = 1`; the Ulam bound
`finrank Q_7a ≤ 1` does not supply that premise. -/
theorem wild_detector_faithful_of_finrank_one
    {distinguishedPlace : Place}
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    [Module (ZMod 59) SelmerChi]
    (hDim : Module.finrank (ZMod 59) (H_FLT SelmerChi) = 1)
    {x₀ : H_FLT SelmerChi} {y₀ : DOmegaSelmerChiStar}
    (htransverse : Lambda wild x₀ y₀ ≠ 0) :
    wild_detector_faithful wild := by
  rw [wild_detector_faithful,
    AddMonoidHom.ker_eq_bot_iff]
  intro a b hab
  have hx₀ : x₀ ≠ 0 := by
    intro hx
    subst x₀
    exact htransverse (by simp)
  have hLambdaX₀ : Lambda wild x₀ ≠ 0 := by
    intro hx
    apply htransverse
    have hxy := DFunLike.congr_fun hx y₀
    simpa using hxy
  have habZero : Lambda wild (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one hDim hx₀ (a - b)
  have hcLambda : c • Lambda wild x₀ = 0 := by
    rw [← ZMod.map_smul (Lambda wild) c x₀, hc, habZero]
  have hcZero : c = 0 :=
    (smul_eq_zero.mp hcLambda).resolve_right hLambdaX₀
  apply sub_eq_zero.mp
  rw [← hc, hcZero, zero_smul]

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

/-! ## The pre-Stage-2 abstract detector interface -/

/-- An abstract dual value with one lamp-selected place above 827.

There is no support field: `wild.toPlaceIndexedLocalPairing` has only the
distinguished column by construction.  In particular, the auxiliary tame
reading is already zero.  Thus this structure is sufficient to index the
existing conditional theorem, but it does not assert a q-relaxed global
Kummer class or compute a transverse 827 coordinate. -/
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

/-- **ABSTRACT INTERFACE — not the Stage-2 witness.**  This proposition is
retained for the compiled conditional route.  An explicit Poitou--Tate
construction must instead inhabit the q-relaxed target audited in
`DetectorWitness827`; the current single-column pairing has no auxiliary
coordinate to realize. -/
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

/-- The scalarized selected gauge vanishes exactly when relation (7a)
holds.  The reverse implication uses only additivity of the supplied
readout; no detector injectivity is involved. -/
theorem scalarGauge_eq_zero_iff_vandiverSevenA
    (comparison : GaugeComparison pair distinguishedPlace wild
      placePrime x d detector) :
    comparison.readout
        (pair.ledger.rootClass 0 + 58 • pair.ledger.rootClass 1) = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  constructor
  · intro hscalar
    apply
      (CommonActionStage.StateLinkedIdealPair.differenceGauge_eq_zero_iff_vandiverSevenA
        pair).mp
    apply comparison.reflects_selected_zero
    rw [CommonActionStage.StateLinkedIdealPair.differenceGauge_reading]
    exact hscalar
  · intro hsevenA
    have hgauge :=
      (CommonActionStage.StateLinkedIdealPair.differenceGauge_eq_zero_iff_vandiverSevenA
        pair).mpr hsevenA
    rw [← CommonActionStage.StateLinkedIdealPair.differenceGauge_reading,
      hgauge, map_zero]

/-- The supplied unit-valued Tate comparison is an exact zero test for
relation (7a), in both directions. -/
theorem local_reading_eq_zero_iff_vandiverSevenA
    (comparison : GaugeComparison pair distinguishedPlace wild
      placePrime x d detector) :
    wild.toPlaceIndexedLocalPairing.pairAt
        distinguishedPlace x detector.detector = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  constructor
  · intro hlocal
    exact comparison.scalarGauge_eq_zero_iff_vandiverSevenA.mp
      (comparison.scalarGauge_eq_zero_of_local_reading_eq_zero hlocal)
  · intro hsevenA
    have hscalar :=
      comparison.scalarGauge_eq_zero_iff_vandiverSevenA.mpr hsevenA
    rw [comparison.pairing_eq_gauge, hscalar, mul_zero]

end GaugeComparison

/-! ## The missing scalar seating on the actual Fermat potential -/

/-- A chosen linear extension of the scalar relation-(7a) gauge to the real
`H_FLT` carrier, together with its value on the selected Fermat class.
Constraining one value does not make the extension or its kernel canonical;
an arithmetic producer must supply the whole map before `Q_7a` is fixed.  No
inhabitant is constructed here. -/
structure SevenAGaugeSeating
    (pair : StateLinkedIdealPair hζ S hz)
    (distinguishedPlace : Place)
    (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)
    (placePrime : Place → ℕ)
    (x : SelmerChi) (d : LampMode)
    (detector : TransverseDetector distinguishedPlace wild placePrime x d)
    (comparison : GaugeComparison pair distinguishedPlace wild
      placePrime x d detector)
    [Module (ZMod 59) SelmerChi] where
  gauge : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59
  gauge_at_fermat :
    gauge x = comparison.readout
      (pair.ledger.rootClass 0 + 58 • pair.ledger.rootClass 1)

namespace SevenAGaugeSeating

variable
  {pair : StateLinkedIdealPair hζ S hz}
  {distinguishedPlace : Place}
  {wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
    (Place := Place) (SelmerChi := SelmerChi)
    (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace}
  {placePrime : Place → ℕ}
  {x : SelmerChi} {d : LampMode}
  {detector : TransverseDetector distinguishedPlace wild placePrime x d}
  {comparison : GaugeComparison pair distinguishedPlace wild
    placePrime x d detector}
  [Module (ZMod 59) SelmerChi]

/-- Once the missing scalar seating is supplied, its Fermat value has the
exact relation-(7a) zero test. -/
theorem gauge_eq_zero_iff_vandiverSevenA
    (seating : SevenAGaugeSeating pair distinguishedPlace wild
      placePrime x d detector comparison) :
    seating.gauge x = 0 ↔ pair.ledger.VandiverSevenA 0 1 := by
  rw [seating.gauge_at_fermat,
    comparison.scalarGauge_eq_zero_iff_vandiverSevenA]

end SevenAGaugeSeating

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
  have hLambda : Lambda wild x = 0 :=
    Lambda_apply_eq_zero_of_reciprocity wild reciprocity x
  have hlocal :
      wild.toPlaceIndexedLocalPairing.pairAt
        distinguishedPlace x detector.detector = 0 :=
    by
      rw [← Lambda_apply]
      exact DFunLike.congr_fun hLambda detector.detector
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
