/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The 827 detector-witness audit

The supporter prime `827 = 2 * 7 * 59 + 1` has a genuine nonzero
power-residue readout: the first entry of the checked circular-unit matrix is
`48` in `ZMod 59`.  This file compares that arithmetic fact with the actual
Selmer carriers used by the tame Tate layer.

Both seated legs are currently character eigenspaces inside Mathlib's
*empty-support* Selmer group.  Their valuations therefore vanish modulo `p`
at every height-one place.  The explicit tame symbol's both-units law (in its
Kummer-quotient, `p`-divisible-valuation form) consequently makes every tame
pairing row zero, including every row above 827 and every fallback auxiliary
prime.

`TransverseDetectorWitness` records the requested honest target modulo the
wild reading: a right-eigenspace candidate, two-place representative support,
and a computed nonzero auxiliary reading.  The generic no-go theorem below
shows that this structure cannot be inhabited with the current empty-support
dual leg.  A construction needs a dual Selmer condition relaxed at the
auxiliary places; replacing the missing class by a zero reading would not be
transverse.

The q-relaxed section uses the vendored finite-`S` sequence in both
directions.  Its range theorem globalizes an S-class torsion element, and its
kernel theorem constructs a literal two-prime S-unit representative once the
projected obstruction is trivial.  The remaining typed gap is a source with
nonzero projected q-coordinate whose two-prime obstruction is the identity,
not merely 59-torsion.
-/
import Fermat.Conservation.TamePlacePairing
import Fermat.Conservation.SelmerSequence
import Fermat.FiftyNine.Conservation.CapacityCertificate

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.DetectorWitness827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TamePlacePairing

/-! ## The executable 827 lamp readout -/

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

/-- The first node of the generated 28-node real unit ledger. -/
def firstLedgerNode : Credit.LedgerNode :=
  ⟨0, by norm_num [Credit.LedgerNode]⟩

/-- The first checked power-residue coordinate at the first place above 827.
It is the row `j = 0`, first generated-edge column `i = 0` entry. -/
def firstLampReading827 : ZMod 59 :=
  CapacityCertificate.generatedMatrix firstLedgerNode firstLedgerNode

/-- The first 827 lamp coordinate is the explicitly computed value `48`. -/
theorem firstLampReading827_eq : firstLampReading827 = 48 := by
  decide +kernel +revert

/-- In particular, the finite 827 lamp is not the zero channel. -/
theorem firstLampReading827_ne_zero : firstLampReading827 ≠ 0 := by
  rw [firstLampReading827_eq]
  decide

/-- The first generated circular-unit edge has residue `105` at the first
selected embedding over 827. -/
theorem firstEdgeResidue827_eq :
    CapacityCertificate.edgeResidue firstLedgerNode firstLedgerNode = 105 := by
  decide +kernel +revert

/-- Its fourteenth-power symbol is the concrete residue `803`. -/
theorem firstEdgeSymbol827_eq :
    CapacityCertificate.edgeResidue firstLedgerNode firstLedgerNode ^ (2 * 7) =
      (803 : ZMod Credit.attestationPrime) := by
  decide +kernel +revert

/-- The same symbol is `671^48`, tying the numerical residue back to the
checked order-59 coordinate rather than treating `48` as uploaded data. -/
theorem firstEdgeSymbol827_eq_root_pow_reading :
    CapacityCertificate.edgeResidue firstLedgerNode firstLedgerNode ^ (2 * 7) =
      Credit.attestationRoot ^ firstLampReading827.val := by
  decide +kernel +revert

/-! ## The actual q-relaxed carrier and the capacity comparison -/

universe uRelaxedK uRelaxedDelta

/-- The height-one places of the cyclotomic integer ring lying over the
auxiliary rational prime `827`.  This is the literal support passed to
Mathlib's `selmerGroup`; it is not a decorative place label. -/
def placesOver827 (K : Type uRelaxedK) [Field K] [NumberField K] :
    Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  {v | Ideal.span ({(Credit.attestationPrime : ℤ)} : Set ℤ) =
    v.asIdeal.under ℤ}

/-- The distinguished wild places over 59, used only in the literal
two-rational-prime representative-support statement. -/
def placesOver59 (K : Type uRelaxedK) [Field K] [NumberField K] :
    Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  {v | Ideal.span ({(59 : ℤ)} : Set ℤ) = v.asIdeal.under ℤ}

@[simp]
theorem mem_placesOver827_iff
    {K : Type uRelaxedK} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    v ∈ placesOver827 K ↔
      Ideal.span ({(Credit.attestationPrime : ℤ)} : Set ℤ) =
        v.asIdeal.under ℤ :=
  Iff.rfl

/-- The auxiliary support is genuinely finite. -/
theorem placesOver827_finite
    (K : Type uRelaxedK) [Field K] [NumberField K] :
    (placesOver827 K).Finite := by
  let qIdeal : Ideal ℤ :=
    Ideal.span ({(Credit.attestationPrime : ℤ)} : Set ℤ)
  have himage :
      IsDedekindDomain.HeightOneSpectrum.asIdeal '' placesOver827 K ⊆
        qIdeal.primesOver (𝓞 K) := by
    rintro I ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, ⟨hv⟩⟩
  apply Set.Finite.of_finite_image
    ((IsDedekindDomain.primesOver_finite qIdeal (𝓞 K)).subset himage)
  intro v _ w _ hvw
  exact IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr hvw

/-- The literal two-prime support allowed for a transverse detector
representative. -/
def detectorSupport827 (K : Type uRelaxedK) [Field K] [NumberField K] :
    Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  placesOver59 K ∪ placesOver827 K

/-- Mathlib's q-relaxed Selmer carrier at all places over 827. -/
abbrev QRelaxedSelmerCarrier827
    (K : Type uRelaxedK) [Field K] [NumberField K] :=
  SelmerEigenspace.SelmerCarrierAt (𝓞 K) K (placesOver827 K) 59

/-- The away-from-827 class obstruction target in the vendored finite-`S`
sequence. -/
abbrev QRelaxedSClassTarget827
    (K : Type uRelaxedK) [Field K] [NumberField K] :=
  IsDedekindDomain.selmerGroup.obstructionTarget
    (R := 𝓞 K) (K := K) (placesOver827 K)

/-- Surjectivity of the vendored finite-`S` class leg: every 59-torsion
away-from-827 class has a genuine q-relaxed global Selmer preimage. -/
theorem exists_qRelaxedSource_of_sClass_torsion
    {K : Type uRelaxedK} [Field K] [NumberField K]
    (c : QRelaxedSClassTarget827 K) (hc : c ^ 59 = 1) :
    ∃ source : QRelaxedSelmerCarrier827 K,
      IsDedekindDomain.selmerGroup.toSClass
          (R := 𝓞 K) (K := K) (n := 59) (placesOver827 K)
            (Additive.toMul source) = c := by
  have hker : c ∈
      (powMonoidHom 59 : QRelaxedSClassTarget827 K →*
        QRelaxedSClassTarget827 K).ker :=
    hc
  rw [← IsDedekindDomain.selmerGroup.toSClass_range
    (R := 𝓞 K) (K := K) (n := 59)] at hker
  obtain ⟨source, hsource⟩ := hker
  exact ⟨Additive.ofMul source, hsource⟩

/-- One global q-relaxed source selected from the finite-`S` surjection. -/
noncomputable def qRelaxedSourceOfSClassTorsion827
    {K : Type uRelaxedK} [Field K] [NumberField K]
    (c : QRelaxedSClassTarget827 K) (hc : c ^ 59 = 1) :
    QRelaxedSelmerCarrier827 K :=
  Classical.choose (exists_qRelaxedSource_of_sClass_torsion c hc)

theorem toSClass_qRelaxedSourceOfSClassTorsion827
    {K : Type uRelaxedK} [Field K] [NumberField K]
    (c : QRelaxedSClassTarget827 K) (hc : c ^ 59 = 1) :
    IsDedekindDomain.selmerGroup.toSClass
        (R := 𝓞 K) (K := K) (n := 59) (placesOver827 K)
          (Additive.toMul (qRelaxedSourceOfSClassTorsion827 c hc)) = c :=
  Classical.choose_spec (exists_qRelaxedSource_of_sClass_torsion c hc)

/-- A supplied Delta action on the literal q-relaxed carrier.  Its type
encodes support stability; constructing the arithmetic Galois action remains
separate from the carrier definition. -/
abbrev QRelaxedSelmerDeltaRepresentation827
    (K : Type uRelaxedK) [Field K] [NumberField K]
    (Delta : Type uRelaxedDelta) [CommGroup Delta] :=
  SelmerEigenspace.SelmerDeltaRepresentationAt
    (R := 𝓞 K) (K := K) (p := 59) (Delta := Delta) (placesOver827 K)

/-- The reflected-character projector target on the q-relaxed carrier. -/
abbrev QRelaxedReflectedDual827
    {K : Type uRelaxedK} [Field K] [NumberField K]
    {Delta : Type uRelaxedDelta} [CommGroup Delta]
    (rhoQ : QRelaxedSelmerDeltaRepresentation827 K Delta)
    (omega chi : InvolutiveBase.Character (PadicInt 59) Delta) :=
  SelmerEigenspace.DOmegaSelmerChiStarAt rhoQ omega chi

variable {K59 : Type uRelaxedK} [Field K59] [NumberField K59]
  [IsCyclotomicExtension {59} ℚ K59]

local instance : Module ℤ (CapacityCertificate.UnitLattice K59) :=
  @AddCommGroup.toIntModule
    (CapacityCertificate.UnitLattice K59) inferInstance

/-- The first capacity row as an actual functional on the Dirichlet unit
lattice. -/
noncomputable def firstResidueFunctional827
    (hζ : IsPrimitiveRoot (ζ : K59) 59) :
    CapacityCertificate.UnitLattice K59 →ₗ[ℤ] ZMod 59 :=
  CapacityCertificate.residueFunctional hζ firstLedgerNode

/-- Evaluating the actual first capacity functional on the actual first
generated unit gives the lamp coordinate used by the detector. -/
theorem firstResidueFunctional827_generatedUnit
    (hζ : IsPrimitiveRoot (ζ : K59) 59) :
    firstResidueFunctional827 hζ
        (CapacityCertificate.unitClass
          (Credit.generatedUnit hζ firstLedgerNode : (𝓞 K59)ˣ)) =
      firstLampReading827 := by
  exact CapacityCertificate.residueFunctional_generatedUnit_eq
    hζ firstLedgerNode firstLedgerNode

section RelaxedProjectorAndLocalization

variable {K : Type uRelaxedK} [Field K] [NumberField K]
  {Delta : Type uRelaxedDelta} [CommGroup Delta] [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt 59)]
  (rhoQ : QRelaxedSelmerDeltaRepresentation827 K Delta)
  (omega chi : InvolutiveBase.Character (PadicInt 59) Delta)

/-- The genuine reflected-character idempotent on the q-relaxed carrier. -/
noncomputable def qRelaxedReflectedProjector827 :
    QRelaxedSelmerCarrier827 K →ₗ[PadicInt 59]
      QRelaxedReflectedDual827 rhoQ omega chi :=
  SelmerEigenspace.characterProjectorAt rhoQ
    (InvolutiveBase.reflectedCharacter omega chi)

/-- One selected 827-coordinate of Mathlib's supported Selmer valuation. -/
def qLocalizationCoordinate827
    (v827 : {v // v ∈ placesOver827 K}) :
    QRelaxedReflectedDual827 rhoQ omega chi →+ ZMod 59 :=
  SelmerEigenspace.eigenspaceSupportValuationAt rhoQ
    (InvolutiveBase.reflectedCharacter omega chi) v827

/-- Multiplication by the actual first capacity-functional value. -/
def firstLampScale827 : ZMod 59 →+ ZMod 59 where
  toFun m := m * firstLampReading827
  map_zero' := by simp
  map_add' := by intros; ring

/-- The comparison readout obtained by multiplying the selected q-valuation
by the explicit first residue functional.  Equality with an actual local tame
pairing is a separate local-realization statement below. -/
def localizationResidueReadout827
    (v827 : {v // v ∈ placesOver827 K}) :
    QRelaxedReflectedDual827 rhoQ omega chi →+ ZMod 59 :=
  firstLampScale827.comp (qLocalizationCoordinate827 rhoQ omega chi v827)

omit [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt 59)] in
@[simp]
theorem localizationResidueReadout827_apply
    (v827 : {v // v ∈ placesOver827 K})
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    localizationResidueReadout827 rhoQ omega chi v827 y =
      qLocalizationCoordinate827 rhoQ omega chi v827 y *
        firstLampReading827 :=
  rfl

omit [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt 59)] in
/-- The comparison coefficient is literally the capacity functional
evaluated on the first generated unit. -/
theorem localizationResidueReadout827_eq_mul_residueFunctional
    [IsCyclotomicExtension {59} ℚ K]
    (hζ : IsPrimitiveRoot (ζ : K) 59)
    (v827 : {v // v ∈ placesOver827 K})
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    localizationResidueReadout827 rhoQ omega chi v827 y =
      qLocalizationCoordinate827 rhoQ omega chi v827 y *
        firstResidueFunctional827 hζ
          (CapacityCertificate.unitClass
            (Credit.generatedUnit hζ firstLedgerNode : (𝓞 K)ˣ)) := by
  rw [firstResidueFunctional827_generatedUnit]
  rfl

omit [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt 59)] in
/-- A nonzero selected q-valuation gives a nonzero computed 827 readout. -/
theorem localizationResidueReadout827_ne_zero
    (v827 : {v // v ∈ placesOver827 K})
    (y : QRelaxedReflectedDual827 rhoQ omega chi)
    (hy : qLocalizationCoordinate827 rhoQ omega chi v827 y ≠ 0) :
    localizationResidueReadout827 rhoQ omega chi v827 y ≠ 0 := by
  rw [localizationResidueReadout827_apply]
  exact mul_ne_zero hy firstLampReading827_ne_zero

/-- Regard the projected q-relaxed candidate as a Selmer class relaxed at
both rational primes allowed in the final representative support. -/
noncomputable def projectedCandidateAtDetectorSupport827
    (source : QRelaxedSelmerCarrier827 K) :
    IsDedekindDomain.selmerGroup
      (R := 𝓞 K) (K := K) (S := detectorSupport827 K) (n := 59) :=
  Subgroup.inclusion
    (IsDedekindDomain.selmerGroup.monotone
      (show placesOver827 K ⊆ detectorSupport827 K from Set.subset_union_right))
    (Additive.toMul (qRelaxedReflectedProjector827 rhoQ omega chi source).1)

/-- The finite-`S` class obstruction of the actual projected candidate,
computed after enlarging its support from q to the two primes allowed for a
transverse representative. -/
noncomputable def projectedCandidateSClassObstruction827
    (source : QRelaxedSelmerCarrier827 K) :
    IsDedekindDomain.selmerGroup.obstructionTarget
      (R := 𝓞 K) (K := K) (detectorSupport827 K) :=
  IsDedekindDomain.selmerGroup.toSClass
    (R := 𝓞 K) (K := K) (n := 59) (detectorSupport827 K)
      (projectedCandidateAtDetectorSupport827 rhoQ omega chi source)

/-- The vendored finite-`S` range theorem proves that every projected
candidate obstruction is 59-torsion.  The lift needs the stronger statement
that this particular torsion class is the identity. -/
theorem projectedCandidateSClassObstruction827_pow_eq_one
    (source : QRelaxedSelmerCarrier827 K) :
    projectedCandidateSClassObstruction827 rhoQ omega chi source ^ 59 = 1 := by
  have hmem :
      projectedCandidateSClassObstruction827 rhoQ omega chi source ∈
        (IsDedekindDomain.selmerGroup.toSClass
          (R := 𝓞 K) (K := K) (n := 59) (detectorSupport827 K)).range :=
    ⟨projectedCandidateAtDetectorSupport827 rhoQ omega chi source, rfl⟩
  rw [IsDedekindDomain.selmerGroup.toSClass_range
    (R := 𝓞 K) (K := K) (n := 59)] at hmem
  exact MonoidHom.mem_ker.mp hmem

/-- **The first new typed obligation after q-relaxation.**

The candidate is produced by the actual character projector, has a nonzero
coordinate under Mathlib's supported valuation, and retains a representative
whose literal divisor is supported over 59 and 827.  The arbitrary-support
carrier and projector do not construct an inhabitant of this structure. -/
structure ReflectedQRelaxedLocalizationLift827 where
  source : QRelaxedSelmerCarrier827 K
  selectedPlace : {v // v ∈ placesOver827 K}
  selectedLocalization_ne_zero :
    qLocalizationCoordinate827 rhoQ omega chi selectedPlace
        (qRelaxedReflectedProjector827 rhoQ omega chi source) ≠ 0
  candidateRepresentative : Kˣ
  candidate_represents :
    (candidateRepresentative :
      Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) =
      SelmerEigenspace.toKummerQuotientAt
        (qRelaxedReflectedProjector827 rhoQ omega chi source)
  representative_support : ∀ v,
    v ∉ placesOver59 K → v ∉ placesOver827 K →
      (v.valuationOfNeZero candidateRepresentative).toAdd = 0

namespace ReflectedQRelaxedLocalizationLift827

variable {rhoQ omega chi}

/-- The finite-`S` kernel theorem supplies the matching representative once
the projected candidate's two-prime S-class obstruction is trivial.  This
constructor reduces the lift to the joint existence of a source and selected
place with nonzero q-coordinate and identity, rather than merely 59-torsion,
of this obstruction. -/
noncomputable def ofSource_of_sClassObstruction_eq_one
    (source : QRelaxedSelmerCarrier827 K)
    (selectedPlace : {v // v ∈ placesOver827 K})
    (hcoord :
      qLocalizationCoordinate827 rhoQ omega chi selectedPlace
          (qRelaxedReflectedProjector827 rhoQ omega chi source) ≠ 0)
    (hobs :
      projectedCandidateSClassObstruction827 rhoQ omega chi source = 1) :
    ReflectedQRelaxedLocalizationLift827 rhoQ omega chi := by
  have hker :
      projectedCandidateAtDetectorSupport827 rhoQ omega chi source ∈
        (IsDedekindDomain.selmerGroup.toSClass
          (R := 𝓞 K) (K := K) (n := 59) (detectorSupport827 K)).ker := by
    exact hobs
  rw [IsDedekindDomain.selmerGroup.toSClass_ker
    (R := 𝓞 K) (K := K)] at hker
  let q := Classical.choose hker
  have hq := Classical.choose_spec hker
  let u : (detectorSupport827 K).unit K := q.out
  have hu : QuotientGroup.mk u = q := QuotientGroup.out_eq' q
  have hqu :
      IsDedekindDomain.selmerGroup.fromSUnitLift
          (R := 𝓞 K) (K := K) (n := 59) (detectorSupport827 K)
            (QuotientGroup.mk u) =
        projectedCandidateAtDetectorSupport827 rhoQ omega chi source := by
    rw [hu]
    exact hq
  refine
    { source := source
      selectedPlace := selectedPlace
      selectedLocalization_ne_zero := hcoord
      candidateRepresentative := (u : Kˣ)
      candidate_represents := ?_
      representative_support := ?_ }
  · exact congr_arg Subtype.val hqu
  · intro v hp hq'
    have hv : v ∉ detectorSupport827 K := by
      intro hv
      rcases hv with hv | hv
      · exact hp hv
      · exact hq' hv
    have hzero :
        (v.valuationOfNeZero (u : Kˣ)).toAdd = 0 ↔
          v.valuation K (u : Kˣ) = 1 := by
      rw [← v.valuationOfNeZero_eq (u : Kˣ), ← WithZero.coe_one,
        WithZero.coe_inj]
      rfl
    exact hzero.mpr
      (Set.unit_valuation_eq_one (detectorSupport827 K) K u hv)

/-- A sufficient combined finite-`S` route.  The range theorem first chooses
a global preimage of a 59-torsion away-from-827 class; the kernel theorem then
supplies the literal two-prime representative after projection.  Since the
preimage is chosen noncomputably, this constructor does not characterize all
possible good preimages. -/
noncomputable def ofSClassTorsion_of_projected_obstruction_eq_one
    (c : QRelaxedSClassTarget827 K) (hc : c ^ 59 = 1)
    (selectedPlace : {v // v ∈ placesOver827 K})
    (hcoord :
      qLocalizationCoordinate827 rhoQ omega chi selectedPlace
          (qRelaxedReflectedProjector827 rhoQ omega chi
            (qRelaxedSourceOfSClassTorsion827 c hc)) ≠ 0)
    (hobs :
      projectedCandidateSClassObstruction827 rhoQ omega chi
          (qRelaxedSourceOfSClassTorsion827 c hc) = 1) :
    ReflectedQRelaxedLocalizationLift827 rhoQ omega chi :=
  ofSource_of_sClassObstruction_eq_one
    (qRelaxedSourceOfSClassTorsion827 c hc) selectedPlace hcoord hobs

/-- The projected candidate, named for downstream witness construction. -/
noncomputable def candidate
    (lift : ReflectedQRelaxedLocalizationLift827 rhoQ omega chi) :
    QRelaxedReflectedDual827 rhoQ omega chi :=
  qRelaxedReflectedProjector827 rhoQ omega chi lift.source

/-- Eigenspace membership is constructed, not stored as a field. -/
theorem candidate_eigenlaw
    (lift : ReflectedQRelaxedLocalizationLift827 rhoQ omega chi)
    (delta : Delta) :
    rhoQ delta lift.candidate.1 =
      (InvolutiveBase.reflectedCharacter omega chi delta : PadicInt 59) •
        lift.candidate.1 :=
  (SelmerEigenspace.mem_characterEigenspaceAt_iff rhoQ
    (InvolutiveBase.reflectedCharacter omega chi) lift.candidate.1).mp
      lift.candidate.property delta

/-- The computed capacity readout attached to the lifted candidate. -/
def computedQReading
    (lift : ReflectedQRelaxedLocalizationLift827 rhoQ omega chi) : ZMod 59 :=
  localizationResidueReadout827 rhoQ omega chi lift.selectedPlace lift.candidate

theorem computedQReading_ne_zero
    (lift : ReflectedQRelaxedLocalizationLift827 rhoQ omega chi) :
    lift.computedQReading ≠ 0 :=
  localizationResidueReadout827_ne_zero rhoQ omega chi
    lift.selectedPlace lift.candidate lift.selectedLocalization_ne_zero

/-- The first generated circular unit, embedded into the cyclotomic field,
is the primal representative tested by the capacity row. -/
noncomputable def primalRepresentative
    [IsCyclotomicExtension {59} ℚ K]
    (hζ : IsPrimitiveRoot (ζ : K) 59) : Kˣ :=
  Units.map (algebraMap (𝓞 K) K)
    (Credit.generatedUnit hζ firstLedgerNode : (𝓞 K)ˣ)

/-- Outside the two rational primes 59 and 827, the literal support receipt
and the fact that the primal entry is a global unit feed the existing
both-units law directly. -/
theorem outside_reading_eq_zero_of_both_units
    [IsCyclotomicExtension {59} ℚ K]
    (hζ : IsPrimitiveRoot (ζ : K) 59)
    (lift : ReflectedQRelaxedLocalizationLift827 rhoQ omega chi)
    {k : Type*} [Fintype k] [Field k]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ctx : TameSymbol.Context 59 K k)
    (ord_eq_valuation : ∀ a,
      ctx.ord (Additive.ofMul a) = (v.valuationOfNeZero a).toAdd)
    (hp : v ∉ placesOver59 K) (hq : v ∉ placesOver827 K) :
    ctx.value (primalRepresentative hζ) lift.candidateRepresentative = 0 := by
  apply ctx.both_units_silence
  · rw [ord_eq_valuation]
    exact congrArg Multiplicative.toAdd
      (v.valuation_of_unit_eq
        (Credit.generatedUnit hζ firstLedgerNode : (𝓞 K)ˣ))
  · rw [ord_eq_valuation]
    exact lift.representative_support v hp hq

/-- The remaining local realization interface at the selected q-place.
It identifies the explicit tame symbol with the already constructed
localization/residue-functional comparison; it neither chooses the global
lift nor hides the angular-component construction. -/
structure SelectedTameComparison
    [IsCyclotomicExtension {59} ℚ K]
    (hζ : IsPrimitiveRoot (ζ : K) 59)
    (lift : ReflectedQRelaxedLocalizationLift827 rhoQ omega chi)
    (k : Type*) [Fintype k] [Field k]
    (ctx : TameSymbol.Context 59 K k) : Prop where
  ord_eq_valuation : ∀ a,
    ctx.ord (Additive.ofMul a) =
      (lift.selectedPlace.1.valuationOfNeZero a).toAdd
  reading_eq_computed :
    ctx.value (primalRepresentative hζ) lift.candidateRepresentative =
      lift.computedQReading

/-- Once the named local comparison is supplied, the selected actual tame
reading is nonzero and equals the capacity-functional readout. -/
theorem selected_tame_reading_ne_zero
    [IsCyclotomicExtension {59} ℚ K]
    (hζ : IsPrimitiveRoot (ζ : K) 59)
    (lift : ReflectedQRelaxedLocalizationLift827 rhoQ omega chi)
    {k : Type*} [Fintype k] [Field k]
    (ctx : TameSymbol.Context 59 K k)
    (comparison : SelectedTameComparison hζ lift k ctx) :
    ctx.value (primalRepresentative hζ) lift.candidateRepresentative ≠ 0 := by
  rw [comparison.reading_eq_computed]
  exact lift.computedQReading_ne_zero

end ReflectedQRelaxedLocalizationLift827

end RelaxedProjectorAndLocalization

/-! ## The honest q-relaxed target, with the wild value omitted -/

universe uTargetK uTargetPlace uTargetResidue uTargetDelta uTargetDual

/-- The actual construction target for one auxiliary supporter prime.

`tame_away_from_wild` makes every place not over `p` part of the tame locus.
`candidate_relaxed_valuation` is the defining local condition of the Selmer
group relaxed at the places over `p` and `q`.  The explicit representative
support fields strengthen this to literal valuation zero away from those
places, so `outside_tame_reading_eq_zero` below follows from the both-units
law.  `right_eigenlaw` records the reflected-character leg without assuming
an unconstructed global Galois action.  The q-readings are explicit tame
symbols and at least one is required to be nonzero.  There is deliberately no
wild-reading field. -/
structure TransverseDetectorWitness
    (p q k : ℕ) [Fact p.Prime]
    (K : Type uTargetK) [Field K]
    (Place : Type uTargetPlace)
    (placePrime : Place → ℕ)
    (Residue : Place → Type uTargetResidue)
    [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
    (IsTame : Place → Prop)
    (context : ∀ v, IsTame v → TameSymbol.Context p K (Residue v))
    (Delta : Type uTargetDelta) [CommGroup Delta]
    (omega chi : InvolutiveBase.Character (PadicInt p) Delta)
    (Dual : Type uTargetDual) [AddCommGroup Dual] [Module (PadicInt p) Dual]
    (dualAction : Representation (PadicInt p) Delta Dual)
    (dualClass : Dual →+ TameSymbol.KummerClass p K)
    (primalClass : TameSymbol.KummerClass p K) where
  auxiliary_prime : q.Prime
  supporter_relation : q = 2 * k * p + 1
  tame_away_from_wild : ∀ v, placePrime v ≠ p → IsTame v
  candidate : Dual
  right_eigenlaw : ∀ delta,
    dualAction delta candidate =
      (InvolutiveBase.reflectedCharacter omega chi delta : PadicInt p) •
        candidate
  candidate_relaxed_valuation : ∀ v (hv : IsTame v),
    placePrime v ≠ p → placePrime v ≠ q →
      (context v hv).ordModP (dualClass candidate) = 0
  primalRepresentative : Kˣ
  primal_represents :
    Additive.ofMul (QuotientGroup.mk' _ primalRepresentative) = primalClass
  candidateRepresentative : Kˣ
  candidate_represents :
    Additive.ofMul (QuotientGroup.mk' _ candidateRepresentative) =
      dualClass candidate
  primal_support : ∀ v (hp : placePrime v ≠ p), placePrime v ≠ q →
    (context v (tame_away_from_wild v hp)).ord
      (Additive.ofMul primalRepresentative) = 0
  candidate_support : ∀ v (hp : placePrime v ≠ p), placePrime v ≠ q →
    (context v (tame_away_from_wild v hp)).ord
      (Additive.ofMul candidateRepresentative) = 0
  qReadings : Place → ZMod p
  qReadings_computed : ∀ v (_hq : placePrime v = q) (hv : IsTame v),
    qReadings v =
      (context v hv).value primalRepresentative candidateRepresentative
  transverse : ∃ v, placePrime v = q ∧ IsTame v ∧ qReadings v ≠ 0

namespace TransverseDetectorWitness

variable
  {p q k : ℕ} [Fact p.Prime]
  {K : Type uTargetK} [Field K]
  {Place : Type uTargetPlace}
  {placePrime : Place → ℕ}
  {Residue : Place → Type uTargetResidue}
  [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
  {IsTame : Place → Prop}
  {context : ∀ v, IsTame v → TameSymbol.Context p K (Residue v)}
  {Delta : Type uTargetDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt p) Delta}
  {Dual : Type uTargetDual} [AddCommGroup Dual] [Module (PadicInt p) Dual]
  {dualAction : Representation (PadicInt p) Delta Dual}
  {dualClass : Dual →+ TameSymbol.KummerClass p K}
  {primalClass : TameSymbol.KummerClass p K}

/-- Outside the wild and auxiliary rational primes, literal representative
support makes both entries units, so the explicit both-units law computes
the tame symbol as zero. -/
theorem outside_tame_reading_eq_zero
    (w : TransverseDetectorWitness p q k K Place placePrime Residue IsTame
      context Delta omega chi Dual dualAction dualClass primalClass)
    (v : Place) (hp : placePrime v ≠ p) (hq : placePrime v ≠ q) :
    (context v (w.tame_away_from_wild v hp)).value
      w.primalRepresentative w.candidateRepresentative = 0 :=
  (context v (w.tame_away_from_wild v hp)).both_units_silence
    w.primalRepresentative w.candidateRepresentative
    (w.primal_support v hp hq) (w.candidate_support v hp hq)

end TransverseDetectorWitness

/-! ## Attempting the target on the current seated carrier -/

namespace Seated

universe uR uK uk uDelta

variable {p auxiliaryPrime : ℕ} [Fact p.Prime]
  {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt p) Delta}
  {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
    (Delta := Delta)}

abbrev Place := TamePlacePairing.Seated.Place (R := R)

abbrev Primal := TamePlacePairing.Seated.Primal
  (rho := rho) (chi := chi)

abbrev ReflectedDual := TamePlacePairing.Seated.ReflectedDual
  (rho := rho) (omega := omega) (chi := chi)

abbrev Pairing := TamePlacePairing.Seated.Pairing
  (p := p) (Delta := Delta) (omega := omega) (chi := chi)
  (R := R) (K := K) (rho := rho)

/-- The requested transverse-detector data *except* the wild reading.

The candidate is literally in the reflected-character eigenspace.  The
support field is stated for its canonical Kummer representative and says
that all integer valuations outside the distinguished and auxiliary places
are zero.  `auxiliaryReading_ne_zero` is what makes the auxiliary coordinate
transverse; omitting it would allow the zero candidate to masquerade as the
witness. -/
structure EmptySupportTransverseDetectorWitness
    (pairing : Pairing (p := p) (Delta := Delta) (omega := omega)
      (chi := chi) (R := R) (K := K) (rho := rho))
    (Residue : Place (R := R) → Type uk)
    [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
    (IsTame : Place (R := R) → Prop)
    (realization : TamePlacePairing.Seated.Realization pairing Residue IsTame)
    (placePrime : Place (R := R) → ℕ)
    (distinguished auxiliary : Place (R := R))
    (x : Primal (rho := rho) (chi := chi)) where
  candidate : ReflectedDual (rho := rho) (omega := omega) (chi := chi)
  auxiliary_ne_distinguished : auxiliary ≠ distinguished
  distinguished_liesOver : placePrime distinguished = p
  auxiliary_liesOver : placePrime auxiliary = auxiliaryPrime
  auxiliary_tame : IsTame auxiliary
  representative_support : ∀ v,
    v ≠ distinguished → v ≠ auxiliary →
      (v.valuationOfNeZero
        (SelmerEigenspace.quotientRepresentative candidate)).toAdd = 0
  auxiliaryReading : ZMod p
  auxiliaryReading_computed :
    pairing.pairAt auxiliary x candidate = auxiliaryReading
  auxiliaryReading_ne_zero : auxiliaryReading ≠ 0

namespace EmptySupportTransverseDetectorWitness

variable
  {pairing : Pairing (p := p) (Delta := Delta) (omega := omega)
    (chi := chi) (R := R) (K := K) (rho := rho)}
  {Residue : Place (R := R) → Type uk}
  [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
  {IsTame : Place (R := R) → Prop}
  {realization : TamePlacePairing.Seated.Realization pairing Residue IsTame}
  {placePrime : Place (R := R) → ℕ}
  {distinguished auxiliary : Place (R := R)}
  {x : Primal (rho := rho) (chi := chi)}

/-- The candidate's type is the requested right/reflected eigenspace, and
unfolding subtype membership gives its explicit eigenvalue law. -/
theorem candidate_eigenlaw
    (w : EmptySupportTransverseDetectorWitness (auxiliaryPrime := auxiliaryPrime)
      pairing Residue IsTame realization placePrime distinguished auxiliary x)
    (delta : Delta) :
    rho delta w.candidate.1 =
      (InvolutiveBase.reflectedCharacter omega chi delta : PadicInt p) •
        w.candidate.1 :=
  (SelmerEigenspace.mem_characterEigenspace_iff
    rho (InvolutiveBase.reflectedCharacter omega chi) w.candidate.1).mp
      w.candidate.property delta

/-- Empty-support Selmer membership already forces the candidate valuation
to be divisible by `p` at every place, independently of its stronger
two-place integer-support certificate. -/
theorem candidate_valuation_dvd
    (w : EmptySupportTransverseDetectorWitness (auxiliaryPrime := auxiliaryPrime)
      pairing Residue IsTame realization placePrime distinguished auxiliary x)
    (v : Place (R := R)) :
    (p : ℤ) ∣
      (v.valuationOfNeZero
        (SelmerEigenspace.quotientRepresentative w.candidate)).toAdd :=
  SelmerEigenspace.quotientRepresentative_valuation_dvd v w.candidate

/-- The both-units law on the Kummer quotient silences every tame reading
of the two current empty-support seated legs.  No property of the numerical
auxiliary prime is used, so changing 827 to any fallback cannot repair this
carrier mismatch. -/
theorem reading_eq_zero_at_every_tame_auxiliary
    (realization : TamePlacePairing.Seated.Realization pairing Residue IsTame)
    (v : Place (R := R)) (hv : IsTame v)
    (x : Primal (rho := rho) (chi := chi))
    (y : ReflectedDual (rho := rho) (omega := omega) (chi := chi)) :
    pairing.pairAt v x y = 0 :=
  realization.pairAt_eq_zero_at_tame_place v hv x y

/-- Hence the supposedly computed transverse coordinate of any proposed
witness is forced to zero. -/
theorem auxiliaryReading_eq_zero
    (w : EmptySupportTransverseDetectorWitness (auxiliaryPrime := auxiliaryPrime)
      pairing Residue IsTame realization placePrime distinguished auxiliary x) :
    w.auxiliaryReading = 0 := by
  rw [← w.auxiliaryReading_computed]
  exact reading_eq_zero_at_every_tame_auxiliary realization auxiliary
    w.auxiliary_tame x w.candidate

/-- **Generic fallback no-go.**  There is no transverse detector witness in
the current empty-support reflected Selmer leg at any tame auxiliary prime.
This covers 827 and every later prime in the generation-chain fallback list. -/
theorem not_nonempty
    (pairing : Pairing (p := p) (Delta := Delta) (omega := omega)
      (chi := chi) (R := R) (K := K) (rho := rho))
    (Residue : Place (R := R) → Type uk)
    [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
    (IsTame : Place (R := R) → Prop)
    (realization : TamePlacePairing.Seated.Realization pairing Residue IsTame)
    (placePrime : Place (R := R) → ℕ)
    (distinguished auxiliary : Place (R := R))
    (x : Primal (rho := rho) (chi := chi)) :
    ¬ Nonempty
      (EmptySupportTransverseDetectorWitness (auxiliaryPrime := auxiliaryPrime)
        pairing Residue IsTame realization placePrime
          distinguished auxiliary x) := by
  rintro ⟨w⟩
  exact w.auxiliaryReading_ne_zero (auxiliaryReading_eq_zero w)

end EmptySupportTransverseDetectorWitness

/-! ## The concrete lamp/seated mismatch at 827 -/

variable
  {Delta : Type uDelta} [CommGroup Delta]
  {omega chi : InvolutiveBase.Character (PadicInt 59) Delta}
  {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
    (Delta := Delta)}
  {pairing : Pairing (p := 59) (Delta := Delta) (omega := omega)
    (chi := chi) (R := R) (K := K) (rho := rho)}
  {Residue : Place (R := R) → Type uk}
  [∀ v, Fintype (Residue v)] [∀ v, Field (Residue v)]
  {IsTame : Place (R := R) → Prop}

/-- The concrete nonzero lamp coordinate `48` cannot be the tame pairing of
two classes in the current seated legs at a place over 827: that pairing is
forced to zero before the residue calculation is consulted. -/
theorem firstLampReading827_not_realized_by_seated_pairing
    (realization : TamePlacePairing.Seated.Realization pairing Residue IsTame)
    (v827 : Place (R := R)) (hv827 : IsTame v827)
    (x : Primal (rho := rho) (chi := chi))
    (y : ReflectedDual (rho := rho) (omega := omega) (chi := chi)) :
    pairing.pairAt v827 x y ≠ firstLampReading827 := by
  rw [EmptySupportTransverseDetectorWitness.reading_eq_zero_at_every_tame_auxiliary
    realization v827 hv827 x y]
  exact Ne.symm firstLampReading827_ne_zero

end Seated

end Fermat.FiftyNine.Conservation.DetectorWitness827
