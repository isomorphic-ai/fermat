/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Ulam W1: conserve the 827 fiber; process the quotient

This is the conductor-59, auxiliary-prime-827 instance of
`ReadoutLedger`.  The public reflected carrier is the complete normalized
fiber of the seated 827 boundary functional.  A normalized element is only
a receipt; no distinguished probe, complement, section, or product splitting
is exported.

The 59-local extension and its lawfulness are separated.  Localization at
59 constructs the old W0 extension surface.  If its restriction to the
conserved 827 kernel is zero, `ReadoutLedger` produces the unique rank-one
coefficient.  If it is nonzero, the retained direction is a STEERABLE bit,
not an implementation failure.

The relation-(7a) gauge remains class-valued in the actual 59-torsion class
carrier.  Its comparison with the wild scalar coefficient is the canonical
equivalence of processed ranges induced by equality of kernels; scalar
proportionality is never used as the invariant.
-/
import Fermat.Conservation.ReadoutLedger
import Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59
import Fermat.FiftyNine.Conservation.TransversalityVerdict827
import Fermat.FiftyNine.Conservation.UlamTypeFreeze

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.UlamReadout827

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.ReadoutLedger
open Fermat.Conservation.TamePlacePairing
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.GaugeAsNaturalityDefect59
open Fermat.FiftyNine.Conservation.PointedTateIncidence
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StateFactorPair
open Fermat.FiftyNine.Conservation.TateBridge
open Fermat.FiftyNine.Conservation.UlamTypeFreeze

universe uPlace uSelmer uDual uClass uUnit uRoot

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  (rhoQ : QRelaxedSelmerDeltaRepresentation827 K GaloisIndex59)
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
  (selectedPlace : Place827 K)

noncomputable local instance instQRelaxedReflectedDual827ModuleZMod :
    Module (ZMod 59) (QRelaxedReflectedDual827 rhoQ omega chi) :=
  AddCommGroup.zmodModule
    (qRelaxedReflectedDual827_nsmul_eq_zero rhoQ omega chi)

/-! ## Step 1: the boundary functional is nonzero -/

/-- The banked Fourier landing and pointed Poitou--Tate incidence force the
actual 827 boundary functional to be nonzero.  Both existing arithmetic
interfaces remain explicit inputs; no normalized class is assumed. -/
theorem reflectedBoundaryFunctional827_ne_zero
    (incidence : PointedTateIncidence827 rhoQ omega chi selectedPlace)
    (seating : QLocalizationEquivariance827 rhoQ omega chi selectedPlace) :
    reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace ≠ 0 := by
  intro hboundary
  have hconnecting :
      incidence.toPoitouTateFiveTerm.connecting = 0 := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro y
    rw [incidence.connecting_apply]
    have hy := LinearMap.congr_fun hboundary y
    rw [reflectedBoundaryFunctional827_apply] at hy
    simpa using congrArg (fun c : ZMod 59 ↦ c * a) hy
  have hgain := reflectedGain_eq_one_of_fourierSeating
    rhoQ omega chi selectedPlace incidence seating
  rw [PoitouTateFiveTerm.reflectedDualObstructionGain, hconnecting,
    LinearMap.range_zero] at hgain
  simpa using hgain

/-! ## Step 2: identify the seated 827-local coordinate -/

/-- The boundary functional is exactly the selected reflected localization
map, not merely a functional with the same rank. -/
theorem reflectedBoundaryFunctional827_eq_reflectedPointedLocalization827 :
    reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace =
      reflectedPointedLocalization827 rhoQ omega chi selectedPlace := by
  ext y
  exact reflectedBoundaryFunctional827_apply rhoQ omega chi selectedPlace y

/-- Pointwise, the boundary reads Mathlib's supported 827 valuation
coordinate on the reflected-character eigenspace. -/
theorem reflectedBoundaryFunctional827_eq_qLocalizationCoordinate827
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace y =
      qLocalizationCoordinate827 rhoQ omega chi selectedPlace y := by
  rw [reflectedBoundaryFunctional827_apply]
  rfl

/-! ## Step 3: retain the normalized fiber as the public carrier -/

/-- Every reflected q-relaxed class whose seated 827 coordinate is one.
This entire affine fiber, not one selected class, is the public carrier. -/
def NormalizedReflectedFiber827 :=
  ReadoutLedger.NormalizedFiber
    (reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace)

/-- Fourier seating plus pointed incidence makes the normalized fiber
nonempty.  The construction uses the generic rescaling receipt and retains
the rest of the fiber. -/
theorem normalizedReflectedFiber827_nonempty
    (incidence : PointedTateIncidence827 rhoQ omega chi selectedPlace)
    (seating : QLocalizationEquivariance827 rhoQ omega chi selectedPlace) :
    Nonempty (NormalizedReflectedFiber827 rhoQ omega chi selectedPlace) :=
  ReadoutLedger.normalizedFiber_nonempty _
    (reflectedBoundaryFunctional827_ne_zero
      rhoQ omega chi selectedPlace incidence seating)

/-- Any receipted point of the public fiber can be adapted locally to W0's
old witness structure.  The private adapter makes no global choice and the
old structure does not become a public carrier of this module. -/
private def normalizedClassReceiptOfFiber
    {Place : Type uPlace} {SelmerChi : Type uSelmer}
    [AddCommGroup SelmerChi]
    [Module (IntegralPadicGroupAlgebra 59 GaloisIndex59) SelmerChi]
    {DOmegaSelmerChiStar : Type uDual}
    [AddCommGroup DOmegaSelmerChiStar]
    [Module (IntegralPadicGroupAlgebra 59 GaloisIndex59)
      DOmegaSelmerChiStar]
    (distinguishedPlace : Place)
    (wild : WildLocalInterface 59 GaloisIndex59 omega chi Place SelmerChi
      DOmegaSelmerChiStar distinguishedPlace)
    (extension : ReflectedWildCarrierExtension827
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      rhoQ omega chi distinguishedPlace wild)
    (y : NormalizedReflectedFiber827 rhoQ omega chi selectedPlace) :
    NormalizedReflectedClass827 rhoQ omega chi distinguishedPlace wild
      selectedPlace extension where
  yStar := y.1
  normalization := y.2

/-! ## Step 4: extend the wild pairing from localization at 59 -/

variable {Place : Type uPlace} {SelmerChi : Type uSelmer}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra 59 GaloisIndex59) SelmerChi]
  {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra 59 GaloisIndex59)
    DOmegaSelmerChiStar]
  (distinguishedPlace : Place)
  (wild : WildLocalInterface 59 GaloisIndex59 omega chi Place SelmerChi
    DOmegaSelmerChiStar distinguishedPlace)

/-- **LOCALIZATION-AT-59 PRODUCER INTERFACE.**  The arithmetic data needed
to extend the wild pairing consists of an equivariant inclusion of the old
reflected carrier and the actual 59-local bilinear reading on the q-relaxed
carrier.  No extension off a subspace and no chosen complement occurs. -/
structure ReflectedWildLocalizationAt59 where
  oldToQRelaxed :
    DOmegaSelmerChiStar →ₗ[IntegralPadicGroupAlgebra 59 GaloisIndex59]
      QRelaxedReflectedDual827 rhoQ omega chi
  oldToQRelaxed_injective : Function.Injective oldToQRelaxed
  readingAt59 :
    SelmerChi →+ (QRelaxedReflectedDual827 rhoQ omega chi →+ ZMod 59)
  adjoint_law : ∀ a x y,
    readingAt59 (a • x) y =
      readingAt59 x ((InvolutiveBase.hash omega a) • y)
  agrees_with_old : ∀ x y,
    readingAt59 x (oldToQRelaxed y) = wild.reading x y

namespace ReflectedWildLocalizationAt59

variable {rhoQ omega chi distinguishedPlace wild}

/-- Package the actual localized reading as the existing wild-interface
shape. -/
def toWildLocalInterface
    (localization : ReflectedWildLocalizationAt59 rhoQ omega chi
      distinguishedPlace wild) :
    WildLocalInterface 59 GaloisIndex59 omega chi Place SelmerChi
      (QRelaxedReflectedDual827 rhoQ omega chi) distinguishedPlace where
  reading := localization.readingAt59
  adjoint_law := localization.adjoint_law

/-- **Step-4 construction.**  A 59-local realization builds the old W0
extension hole.  The construction consumes only localization and its
equivariant old-carrier inclusion. -/
def toReflectedWildCarrierExtension827
    (localization : ReflectedWildLocalizationAt59 rhoQ omega chi
      distinguishedPlace wild) :
    ReflectedWildCarrierExtension827
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      rhoQ omega chi distinguishedPlace wild where
  oldToQRelaxed := localization.oldToQRelaxed
  oldToQRelaxed_injective := localization.oldToQRelaxed_injective
  qRelaxedWild := localization.toWildLocalInterface
  reading_compatibility := localization.agrees_with_old

@[simp]
theorem toReflectedWildCarrierExtension827_reading
    (localization : ReflectedWildLocalizationAt59 rhoQ omega chi
      distinguishedPlace wild)
    (x : SelmerChi) (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    localization.toReflectedWildCarrierExtension827.qRelaxedWild.reading x y =
      localization.readingAt59 x y :=
  rfl

end ReflectedWildLocalizationAt59

/-! ## Step 5: test lawfulness on the conserved 827 kernel -/

/-- The scalar wild reading selected by one Fermat carrier. -/
def selectedWildFunctional827
    (extension : ReflectedWildCarrierExtension827
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      rhoQ omega chi distinguishedPlace wild)
    (hF : H_FLT SelmerChi) :
    QRelaxedReflectedDual827 rhoQ omega chi →ₗ[ZMod 59] ZMod 59 :=
  (extension.qRelaxedWild.reading hF).toZModLinearMap 59

/-- **ARITHMETIC LAWFULNESS INPUT AT THE SELECTED FERMAT CARRIER.**  The
wild reading uses no reflected degree of freedom beyond the processed 827
coordinate. -/
structure SelectedWildLawfulness827
    (extension : ReflectedWildCarrierExtension827
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      rhoQ omega chi distinguishedPlace wild)
    (hF : H_FLT SelmerChi) : Prop where
  ker_boundary_le_ker_wild :
    (reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace).ker ≤
      (selectedWildFunctional827 rhoQ omega chi distinguishedPlace wild
        extension hF).ker

/-- If lawfulness fails, this is the additional reflected bit processed by
the wild pairing. -/
structure SteerableWildDirection827
    (extension : ReflectedWildCarrierExtension827
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      rhoQ omega chi distinguishedPlace wild)
    (hF : H_FLT SelmerChi) where
  direction : QRelaxedReflectedDual827 rhoQ omega chi
  boundary_zero :
    reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace direction = 0
  wild_ne_zero :
    extension.qRelaxedWild.reading hF direction ≠ 0

/-- Failure of the step-5 inclusion is exactly a retained STEERABLE
direction.  It is data for the next ledger row, not a failed proof state. -/
theorem not_lawful_iff_steerableWildDirection
    (extension : ReflectedWildCarrierExtension827
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      rhoQ omega chi distinguishedPlace wild)
    (hF : H_FLT SelmerChi) :
    ¬ (reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace).ker ≤
        (selectedWildFunctional827 rhoQ omega chi distinguishedPlace wild
          extension hF).ker ↔
      Nonempty (SteerableWildDirection827 rhoQ omega chi selectedPlace
        distinguishedPlace wild extension hF) := by
  constructor
  · intro hnot
    obtain ⟨y, hyq, hywild⟩ := SetLike.not_le_iff_exists.mp hnot
    refine ⟨⟨y, LinearMap.mem_ker.mp hyq, ?_⟩⟩
    exact fun hzero ↦ hywild (LinearMap.mem_ker.mpr hzero)
  · rintro ⟨direction⟩ hle
    exact direction.wild_ne_zero <|
      LinearMap.mem_ker.mp <| hle <|
        LinearMap.mem_ker.mpr direction.boundary_zero

/-- In the lawful branch the newly processed wild range is bottom.  This is
the 827 specialization of the generic fixed readout law. -/
theorem selectedWild_newProcessed_eq_bot
    (extension : ReflectedWildCarrierExtension827
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      rhoQ omega chi distinguishedPlace wild)
    (hF : H_FLT SelmerChi)
    (lawful : SelectedWildLawfulness827 rhoQ omega chi selectedPlace
      distinguishedPlace wild extension hF) :
    ReadoutLedger.newProcessed
        (reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace)
        (selectedWildFunctional827 rhoQ omega chi distinguishedPlace wild
          extension hF) = ⊥ :=
  (ReadoutLedger.fixed_iff_newProcessed_eq_bot _ _).mp
    lawful.ker_boundary_le_ker_wild

/-! ## Step 6: extract the canonical rank-one factor -/

/-- At the selected Fermat carrier, lawfulness gives the unique coefficient
of the 827 boundary coordinate. -/
theorem existsUnique_selectedWildFactorization
    (extension : ReflectedWildCarrierExtension827
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      rhoQ omega chi distinguishedPlace wild)
    (hF : H_FLT SelmerChi)
    (boundary_ne_zero :
      reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace ≠ 0)
    (lawful : SelectedWildLawfulness827 rhoQ omega chi selectedPlace
      distinguishedPlace wild extension hF) :
    ∃! coefficient : ZMod 59,
      ∀ y : QRelaxedReflectedDual827 rhoQ omega chi,
        extension.qRelaxedWild.reading hF y =
          coefficient *
            reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace y :=
  ReadoutLedger.existsUnique_rankOneFactorization _ _ boundary_ne_zero
    lawful.ker_boundary_le_ker_wild

/-- Lawfulness on every carrier is the exact input required for a linear
coefficient `Λ`. -/
structure WildLawfulness827
    (extension : ReflectedWildCarrierExtension827
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      rhoQ omega chi distinguishedPlace wild) : Prop where
  ker_boundary_le_ker_wild : ∀ h : H_FLT SelmerChi,
    (reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace).ker ≤
      (selectedWildFunctional827 rhoQ omega chi distinguishedPlace wild
        extension h).ker

/-- The extended 59-local pairing as a bilinear map over `ZMod 59`. -/
def qRelaxedWildBilinear827
    [Module (ZMod 59) SelmerChi]
    (extension : ReflectedWildCarrierExtension827
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      rhoQ omega chi distinguishedPlace wild) :
    H_FLT SelmerChi →ₗ[ZMod 59]
      QRelaxedReflectedDual827 rhoQ omega chi →ₗ[ZMod 59] ZMod 59 where
  toFun h := selectedWildFunctional827 rhoQ omega chi distinguishedPlace wild
    extension h
  map_add' h₁ h₂ := by
    ext y
    simp [selectedWildFunctional827]
  map_smul' a h := by
    have hlinear :=
      (extension.qRelaxedWild.reading.toZModLinearMap 59).map_smul a h
    ext y
    exact congrArg (fun f :
      QRelaxedReflectedDual827 rhoQ omega chi →+ ZMod 59 ↦ f y) hlinear

/-- The canonical linear coefficient of the lawful extended wild pairing. -/
noncomputable def wildCoefficient827
    [Module (ZMod 59) SelmerChi]
    (extension : ReflectedWildCarrierExtension827
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      rhoQ omega chi distinguishedPlace wild)
    (boundary_ne_zero :
      reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace ≠ 0)
    (lawful : WildLawfulness827 rhoQ omega chi selectedPlace
      distinguishedPlace wild extension) :
    H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59 :=
  Classical.choose <|
    ReadoutLedger.existsUnique_bilinearRankOneFactorization
      (reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace)
      (qRelaxedWildBilinear827 rhoQ omega chi distinguishedPlace wild extension)
      boundary_ne_zero lawful.ker_boundary_le_ker_wild

/-- The extended wild pairing is `Λ ⊗ q` on all lawful carriers. -/
theorem qRelaxedWild_factorization
    [Module (ZMod 59) SelmerChi]
    (extension : ReflectedWildCarrierExtension827
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      rhoQ omega chi distinguishedPlace wild)
    (boundary_ne_zero :
      reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace ≠ 0)
    (lawful : WildLawfulness827 rhoQ omega chi selectedPlace
      distinguishedPlace wild extension)
    (h : H_FLT SelmerChi) (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    extension.qRelaxedWild.reading h y =
      wildCoefficient827 rhoQ omega chi selectedPlace distinguishedPlace wild
          extension boundary_ne_zero lawful h *
        reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace y :=
  (Classical.choose_spec <|
    ReadoutLedger.existsUnique_bilinearRankOneFactorization
      (reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace)
      (qRelaxedWildBilinear827 rhoQ omega chi distinguishedPlace wild extension)
      boundary_ne_zero lawful.ker_boundary_le_ker_wild).1 h y

/-! ## Step 7: compare the genuine class-valued 7a gauge -/

/-- The actual 59-torsion ideal-class carrier of the relation-(7a) gauge. -/
abbrev SevenAGaugeCarrier59 :=
  Fermat.Conservation.CommonActionStage.ClassPTorsion
    (NumberField.RingOfIntegers K) 59

local instance instSevenAGaugeCarrier59ModuleZMod :
    Module (ZMod 59) (SevenAGaugeCarrier59 (K := K)) :=
  AddSubgroup.torsionBy.zmodModule

variable [Module (ZMod 59) SelmerChi]
  {ζ : K} {hζ : IsPrimitiveRoot ζ 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

/-- The selected relation-(7a) word in the real 59-torsion class carrier. -/
def selectedClassGauge59
    (pair : StateLinkedIdealPair hζ S hz) :
    SevenAGaugeCarrier59 (K := K) :=
  Fermat.Conservation.CommonActionStage.differenceGauge
    (SevenAGaugeCarrier59 (K := K))
    (Fermat.Conservation.CommonActionStage.allocatedRootClassPTorsion
        pair.ledger 0,
      Fermat.Conservation.CommonActionStage.allocatedRootClassPTorsion
        pair.ledger 1)

/-- Its underlying class is exactly the already-banked difference gauge. -/
@[simp]
theorem selectedClassGauge59_value
    (pair : StateLinkedIdealPair hζ S hz) :
    (selectedClassGauge59 pair :
      Fermat.Conservation.CommonActionStage.AllocatedClass K) =
      Fermat.Conservation.CommonActionStage.differenceGauge
        (Fermat.Conservation.CommonActionStage.AllocatedClass K)
        (Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.classObstruction
          pair) :=
  rfl

/-- Zero of the genuine class-valued selected gauge is exactly relation
(7a). -/
theorem selectedClassGauge59_eq_zero_iff_vandiverSevenA
    (pair : StateLinkedIdealPair hζ S hz) :
    selectedClassGauge59 pair = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  rw [← Subtype.coe_inj]
  simpa using
    (Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.differenceGauge_eq_zero_iff_vandiverSevenA
      pair)

/-- **CLASS-VALUED 7a SEATING INPUT.**  This replaces W0's arbitrary scalar
readout.  The whole map lands in the actual 59-torsion class carrier and its
selected Fermat value is fixed. -/
structure ClassValuedSevenAGaugeSeating
    (pair : StateLinkedIdealPair hζ S hz) (hF : H_FLT SelmerChi) where
  gauge : H_FLT SelmerChi →ₗ[ZMod 59] SevenAGaugeCarrier59 (K := K)
  gauge_at_fermat : gauge hF = selectedClassGauge59 pair

/-- **KERNEL INTERFACE 1.**  The wild coefficient processes at least the
relation-(7a) question: `ker Λ ≤ ker G`. -/
structure WildProcessesAtLeastSevenA
    {pair : StateLinkedIdealPair hζ S hz} {hF : H_FLT SelmerChi}
    (seating : ClassValuedSevenAGaugeSeating pair hF)
    (lambda : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59) : Prop where
  ker_wild_le_ker_gauge : lambda.ker ≤ seating.gauge.ker

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  [Module (IntegralPadicGroupAlgebra 59 GaloisIndex59) SelmerChi] in
/-- If the wild coefficient is the zero map, saying that it processes at
least the relation-(7a) gauge is exactly saying that the entire class-valued
gauge map is zero. -/
theorem wildProcessesAtLeastSevenA_zero_iff
    {pair : StateLinkedIdealPair hζ S hz} {hF : H_FLT SelmerChi}
    (seating : ClassValuedSevenAGaugeSeating pair hF) :
    WildProcessesAtLeastSevenA seating
        (0 : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59) ↔
      seating.gauge = 0 := by
  constructor
  · intro processes
    apply LinearMap.ext
    intro h
    exact LinearMap.mem_ker.mp
      (processes.ker_wild_le_ker_gauge (by simp))
  · intro hgauge
    refine ⟨?_⟩
    intro h _
    rw [LinearMap.mem_ker, hgauge]
    rfl

/-- **KERNEL INTERFACE 2.**  The wild coefficient uses nothing beyond the
relation-(7a) question and therefore descends to `Q_7a`:
`ker G ≤ ker Λ`. -/
structure WildUsesNothingBeyondSevenA
    {pair : StateLinkedIdealPair hζ S hz} {hF : H_FLT SelmerChi}
    (seating : ClassValuedSevenAGaugeSeating pair hF)
    (lambda : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59) : Prop where
  ker_gauge_le_ker_wild : seating.gauge.ker ≤ lambda.ker

/-- The two separately meaningful arithmetic inclusions give equality of
the conserved unknowns. -/
theorem gaugeKernel_eq_wildKernel
    {pair : StateLinkedIdealPair hζ S hz} {hF : H_FLT SelmerChi}
    (seating : ClassValuedSevenAGaugeSeating pair hF)
    (lambda : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59)
    (processes : WildProcessesAtLeastSevenA seating lambda)
    (nothingBeyond : WildUsesNothingBeyondSevenA seating lambda) :
    seating.gauge.ker = lambda.ker :=
  le_antisymm nothingBeyond.ker_gauge_le_ker_wild
    processes.ker_wild_le_ker_gauge

/-- The invariant comparison of the processed class-valued gauge and the
wild scalar coefficient. -/
noncomputable def gaugeProcessedRangeEquiv827
    {pair : StateLinkedIdealPair hζ S hz} {hF : H_FLT SelmerChi}
    (seating : ClassValuedSevenAGaugeSeating pair hF)
    (lambda : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59)
    (processes : WildProcessesAtLeastSevenA seating lambda)
    (nothingBeyond : WildUsesNothingBeyondSevenA seating lambda) :
    LinearMap.range seating.gauge ≃ₗ[ZMod 59] LinearMap.range lambda :=
  ReadoutLedger.processedRangeEquiv seating.gauge lambda
    (gaugeKernel_eq_wildKernel seating lambda processes nothingBeyond)

/-- The canonical range equivalence sends `G h` to `Λ h`. -/
@[simp]
theorem gaugeProcessedRangeEquiv827_apply
    {pair : StateLinkedIdealPair hζ S hz} {hF : H_FLT SelmerChi}
    (seating : ClassValuedSevenAGaugeSeating pair hF)
    (lambda : H_FLT SelmerChi →ₗ[ZMod 59] ZMod 59)
    (processes : WildProcessesAtLeastSevenA seating lambda)
    (nothingBeyond : WildUsesNothingBeyondSevenA seating lambda)
    (h : H_FLT SelmerChi) :
    gaugeProcessedRangeEquiv827 seating lambda processes nothingBeyond
        ⟨seating.gauge h, LinearMap.mem_range_self seating.gauge h⟩ =
      ⟨lambda h, LinearMap.mem_range_self lambda h⟩ :=
  ReadoutLedger.processedRangeEquiv_apply seating.gauge lambda _ h

/-! ## Step 8: audit the actual 59-torsion depth -/

/-- Every value of the actual class-valued gauge is killed by 59. -/
theorem fiftyNine_nsmul_gauge_eq_zero
    {pair : StateLinkedIdealPair hζ S hz} {hF : H_FLT SelmerChi}
    (seating : ClassValuedSevenAGaugeSeating pair hF)
    (h : H_FLT SelmerChi) :
    59 • seating.gauge h = 0 :=
  AddSubgroup.torsionBy.nsmul (seating.gauge h)

/-- Consequently 59 kills every element of the processed range `im G`. -/
theorem fiftyNine_nsmul_gaugeRange_eq_zero
    {pair : StateLinkedIdealPair hζ S hz} {hF : H_FLT SelmerChi}
    (seating : ClassValuedSevenAGaugeSeating pair hF)
    (z : LinearMap.range seating.gauge) :
    59 • z = 0 := by
  apply Subtype.ext
  exact AddSubgroup.torsionBy.nsmul z.1

/-- In the actual gauge carrier, coefficient 58 is literally negation. -/
theorem fiftyEight_nsmul_eq_neg_in_gaugeCarrier
    (x : SevenAGaugeCarrier59 (K := K)) :
    58 • x = -x := by
  apply eq_neg_of_add_eq_zero_left
  calc
    58 • x + x = 58 • x + 1 • x := by rw [one_nsmul]
    _ = (58 + 1) • x := by rw [add_nsmul]
    _ = 59 • x := by norm_num
    _ = 0 := AddSubgroup.torsionBy.nsmul x

/-- The first-layer depth decomposition is routed through the already-banked
Bockstein/PowerRoot receipt; mod-59 zero discards the correction only in the
first projection. -/
theorem bocksteinDepthDecomposition827
    (pair : StateLinkedIdealPair hζ S hz) :
    integralR0 + (58 : ℤ) • integralR1 =
      (integralR0 - integralR1) + bocksteinPowerRootReceipt :=
  (bocksteinPowerRootReceiptObservation pair).exact_integral_decomposition

/-- In a deeper carrier, if `r₀-r₁ = 59c`, the next-layer potential is
`c+r₁`, never merely `r₁`. -/
theorem deeperGauge_nextLayerPotential
    {A : Type*} [AddCommGroup A] (r₀ r₁ c : A)
    (hdifference : r₀ - r₁ = 59 • c) :
    r₀ + 58 • r₁ = 59 • (c + r₁) := by
  calc
    r₀ + 58 • r₁ = (r₀ - r₁) + 59 • r₁ := by
      module
    _ = 59 • c + 59 • r₁ := by rw [hdifference]
    _ = 59 • (c + r₁) := by rw [nsmul_add]

/-! ## Step 9: typed tame-silence/reciprocity seam only -/

/-- **GLOBAL RECIPROCITY INPUT FOR THE LOCALIZED EXTENSION.**  Tame silence
away from the distinguished place is already built into
`WildLocalInterface.toPlaceIndexedLocalPairing`; this structure supplies the
missing global reciprocity law for that exact pairing.  No inhabitant or
pairing vanishing is asserted here. -/
structure TameSilenceReciprocity827
    (localization : ReflectedWildLocalizationAt59 rhoQ omega chi
      distinguishedPlace wild) : Prop where
  globalReciprocity :
    Fermat.Conservation.TatePairing.GlobalReciprocityLaw
      localization.toReflectedWildCarrierExtension827.qRelaxedWild.toPlaceIndexedLocalPairing

omit [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  [Module (ZMod 59) SelmerChi] in
/-- Reciprocity for the one-column localized pairing forces its complete
wild reading to vanish.  Consequently it supplies lawfulness on the
conserved 827 kernel automatically; no separate kernel premise is needed
once this exact reciprocity interface is available. -/
theorem wildLawfulness827_of_reciprocity
    (localization : ReflectedWildLocalizationAt59 rhoQ omega chi
      distinguishedPlace wild)
    (execution : TameSilenceReciprocity827 rhoQ omega chi distinguishedPlace
      wild localization) :
    WildLawfulness827 rhoQ omega chi selectedPlace distinguishedPlace wild
      localization.toReflectedWildCarrierExtension827 := by
  refine ⟨?_⟩
  intro h y _hy
  rw [LinearMap.mem_ker]
  have hfunctional := Lambda_apply_eq_zero_of_reciprocity
    localization.toReflectedWildCarrierExtension827.qRelaxedWild
    execution.globalReciprocity h
  have hvalue := congrArg (fun reading ↦ reading y) hfunctional
  simpa [selectedWildFunctional827, Lambda, pair_59] using hvalue

/-- For the one-column global pairing, reciprocity annihilates not only the
wild reading but also its canonical rank-one coefficient.  This theorem is
the precise reason that a subsequent `ker Lambda ≤ ker G` premise carries
the whole assertion that the class-valued gauge vanishes. -/
theorem wildCoefficient827_eq_zero_of_reciprocity
    (boundary_ne_zero :
      reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace ≠ 0)
    (localization : ReflectedWildLocalizationAt59 rhoQ omega chi
      distinguishedPlace wild)
    (execution : TameSilenceReciprocity827 rhoQ omega chi distinguishedPlace
      wild localization) :
    wildCoefficient827 rhoQ omega chi selectedPlace distinguishedPlace wild
        localization.toReflectedWildCarrierExtension827 boundary_ne_zero
        (wildLawfulness827_of_reciprocity rhoQ omega chi selectedPlace
          distinguishedPlace wild localization execution) = 0 := by
  have hexists : ∃ y : QRelaxedReflectedDual827 rhoQ omega chi,
      reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace y ≠ 0 := by
    by_contra h
    push Not at h
    apply boundary_ne_zero
    ext y
    exact h y
  obtain ⟨y, hy⟩ := hexists
  apply LinearMap.ext
  intro h
  have hreading :
      localization.toReflectedWildCarrierExtension827.qRelaxedWild.reading
          h y = 0 := by
    have hfunctional := Lambda_apply_eq_zero_of_reciprocity
      localization.toReflectedWildCarrierExtension827.qRelaxedWild
      execution.globalReciprocity h
    have hvalue := congrArg (fun reading ↦ reading y) hfunctional
    simpa [Lambda, pair_59] using hvalue
  have hfactor := qRelaxedWild_factorization
    rhoQ omega chi selectedPlace distinguishedPlace wild
    localization.toReflectedWildCarrierExtension827 boundary_ne_zero
    (wildLawfulness827_of_reciprocity rhoQ omega chi selectedPlace
      distinguishedPlace wild localization execution) h y
  have hproduct :
      wildCoefficient827 rhoQ omega chi selectedPlace distinguishedPlace wild
          localization.toReflectedWildCarrierExtension827 boundary_ne_zero
          (wildLawfulness827_of_reciprocity rhoQ omega chi selectedPlace
            distinguishedPlace wild localization execution) h *
        reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace y = 0 :=
    hfactor.symm.trans hreading
  exact (mul_eq_zero.mp hproduct).resolve_right hy

/-! ## Step 10: typed surviving-kernel route only -/

/-- **SURVIVING KERNEL ROUTE INTERFACE.**  These are only the typed plug
points for a future class-to-unit-to-root route out of the conserved
`ker G`.  This session constructs none of the maps, asserts no exactness or
termination, and does not erase the source kernel. -/
structure SurvivingKernelRoute827
    {pair : StateLinkedIdealPair hζ S hz} {hF : H_FLT SelmerChi}
    (seating : ClassValuedSevenAGaugeSeating pair hF)
    (ClassPotential : Type uClass) [AddCommGroup ClassPotential]
    (UnitPotential : Type uUnit) [AddCommGroup UnitPotential]
    (RootPotential : Type uRoot) [AddCommGroup RootPotential] where
  survivingToClass : seating.gauge.ker →+ ClassPotential
  classToUnit : ClassPotential →+ UnitPotential
  unitToRoot : UnitPotential →+ RootPotential

/-! ## Conditional endpoint -/

/-- Conditional relation-(7a) endpoint.  For any member of the conserved
normalized fiber, global reciprocity kills its wild reading.  Rank-one
factorization then kills `Λ(h_F)`; the one consumed kernel direction sends
that fact to the genuine class-valued gauge, whose banked zero test is
relation (7a).

This theorem consumes the localization, lawfulness, gauge-comparison, and
reciprocity interfaces.  It does not inhabit any of them, does not use the
step-10 route, and proves nothing about the surviving `ker G`. -/
theorem vandiverSevenA_of_readout_interfaces
    (boundary_ne_zero :
      reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace ≠ 0)
    (localization : ReflectedWildLocalizationAt59 rhoQ omega chi
      distinguishedPlace wild)
    (lawful : WildLawfulness827 rhoQ omega chi selectedPlace
      distinguishedPlace wild localization.toReflectedWildCarrierExtension827)
    (pair : StateLinkedIdealPair hζ S hz) (hF : H_FLT SelmerChi)
    (gaugeSeating : ClassValuedSevenAGaugeSeating pair hF)
    (processes : WildProcessesAtLeastSevenA gaugeSeating
      (wildCoefficient827 rhoQ omega chi selectedPlace distinguishedPlace wild
        localization.toReflectedWildCarrierExtension827 boundary_ne_zero lawful))
    (execution : TameSilenceReciprocity827 rhoQ omega chi distinguishedPlace
      wild localization)
    (y : NormalizedReflectedFiber827 rhoQ omega chi selectedPlace) :
    pair.ledger.VandiverSevenA 0 1 := by
  let extension := localization.toReflectedWildCarrierExtension827
  let lambda := wildCoefficient827 rhoQ omega chi selectedPlace
    distinguishedPlace wild extension boundary_ne_zero lawful
  have hwild_zero : extension.qRelaxedWild.reading hF y.1 = 0 := by
    have hfunctional := Lambda_apply_eq_zero_of_reciprocity
      extension.qRelaxedWild execution.globalReciprocity hF
    have hvalue := congrArg (fun reading ↦ reading y.1) hfunctional
    simpa [Lambda_apply] using hvalue
  have hfactor := qRelaxedWild_factorization rhoQ omega chi selectedPlace
    distinguishedPlace wild extension boundary_ne_zero lawful hF y.1
  have hlambda : lambda hF = 0 := by
    rw [y.2, mul_one] at hfactor
    exact hfactor.symm.trans hwild_zero
  have hGaugeKer : hF ∈ gaugeSeating.gauge.ker :=
    processes.ker_wild_le_ker_gauge (LinearMap.mem_ker.mpr hlambda)
  have hGaugeZero := LinearMap.mem_ker.mp hGaugeKer
  rw [gaugeSeating.gauge_at_fermat] at hGaugeZero
  exact (selectedClassGauge59_eq_zero_iff_vandiverSevenA pair).mp hGaugeZero

end Fermat.FiftyNine.Conservation.UlamReadout827
