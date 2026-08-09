/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Pointed Poitou--Tate incidence at 827

For a relaxed observation `G : V → U` and a pointed coordinate
`lambda : Vᵛ`, the strict observation is the literal augmentation
`F = (G, lambda)`.  Thus `ker F` and `ker G` are local conditions on the
same global module.  The first two arrows

`ker F → ker G → Q`

are constructed below and are exact without class field theory.

The continuation

`ker F → ker G → Q → Sel(F*)ᵛ → Sel(G*)ᵛ`

is packaged as `PoitouTateFiveTerm`.  An inhabitant is the named
class-field-theory input; none is manufactured in this file.  Exactness at
`Q` alone implies that the rank gained by primal relaxation plus the rank
gained by the reflected-dual obstruction is `finrank Q`.  At the
one-dimensional 827 line this is the conserved-bit identity.

The conductor-59 specialization seats every map currently present in the
repository: the primal map is the retained pointed conormal restriction and
the reflected boundary is the transpose of the actual reflected-character
827 localization coordinate.  What remains named is precisely their
Poitou--Tate exact incidence, not either map and not a branch bit.
-/
import Fermat.FiftyNine.Conservation.SplitPrimeFourier827
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.PointedTateIncidence

open Fermat.Conservation
open Fermat.Conservation.SteeringFiber
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.GaugeSteering827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

universe uK uV uU uQ uRF uRG uDelta

/-! ## Strict and relaxed conditions on one module -/

variable {k : Type uK} [Field k]
  {V : Type uV} [AddCommGroup V] [Module k V]
  {U : Type uU} [AddCommGroup U] [Module k U]
  {Q : Type uQ} [AddCommGroup Q] [Module k Q]

/-- The strict observation `F = (G, lambda)`. -/
def strictObservation (G : V →ₗ[k] U) (lambda : Module.Dual k V) :
    V →ₗ[k] (U × k) :=
  G.prod lambda

/-- The strict and relaxed local conditions on the same global module,
together with their pointed localization. -/
structure PointedConditions (k : Type uK) (V : Type uV) (Q : Type uQ)
    [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup Q] [Module k Q] where
  strictF : Submodule k V
  relaxedG : Submodule k V
  strict_le_relaxed : strictF ≤ relaxedG
  localization : relaxedG →ₗ[k] Q
  exact_at_relaxed : Function.Exact
    (Submodule.inclusion strict_le_relaxed) localization

namespace PointedConditions

variable (conditions : PointedConditions k V Q)

/-- The first arrow of the five-term sequence. -/
def strictInclusion : conditions.strictF →ₗ[k] conditions.relaxedG :=
  Submodule.inclusion conditions.strict_le_relaxed

theorem strictInclusion_injective :
    Function.Injective conditions.strictInclusion :=
  Submodule.inclusion_injective conditions.strict_le_relaxed

end PointedConditions

/-- The pointed conditions canonically cut out by a lawful observation and
one focus covector.  The strict condition is `ker(G,lambda)`, while the
relaxed condition is `ker G`. -/
def focusConditions (G : V →ₗ[k] U) (lambda : Module.Dual k V) :
    PointedConditions k V k where
  strictF := (strictObservation G lambda).ker
  relaxedG := G.ker
  strict_le_relaxed := by
    rw [strictObservation, LinearMap.ker_prod]
    exact inf_le_left
  localization := FocusConormal.conormalRestriction G lambda
  exact_at_relaxed := by
    rw [LinearMap.exact_iff]
    ext x
    constructor
    · intro hx
      have hxLambda : lambda x.1 = 0 := by
        exact LinearMap.mem_ker.mp hx
      refine ⟨⟨x.1, ?_⟩, rfl⟩
      rw [strictObservation, LinearMap.ker_prod]
      exact ⟨x.property, LinearMap.mem_ker.mpr hxLambda⟩
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      have hy : y.1 ∈ G.ker ⊓ lambda.ker := by
        rw [← LinearMap.ker_prod]
        exact y.property
      exact LinearMap.mem_ker.mp hy.2

@[simp]
theorem focusConditions_strictF
    (G : V →ₗ[k] U) (lambda : Module.Dual k V) :
    (focusConditions G lambda).strictF = (strictObservation G lambda).ker :=
  rfl

@[simp]
theorem focusConditions_relaxedG
    (G : V →ₗ[k] U) (lambda : Module.Dual k V) :
    (focusConditions G lambda).relaxedG = G.ker :=
  rfl

@[simp]
theorem focusConditions_localization
    (G : V →ₗ[k] U) (lambda : Module.Dual k V) :
    (focusConditions G lambda).localization =
      FocusConormal.conormalRestriction G lambda :=
  rfl

/-! ## The named Poitou--Tate five-term interface -/

variable {ReflectedF : Type uRF} [AddCommGroup ReflectedF]
  [Module k ReflectedF]
  {ReflectedG : Type uRG} [AddCommGroup ReflectedG]
  [Module k ReflectedG]

/-- **CLASS-FIELD-THEORY INPUT.**  The pointed Poitou--Tate five-term
sequence

`F → G → Q → Sel(F*)ᵛ → Sel(G*)ᵛ`.

The reflected local condition reverses inclusion, hence
`reflectedGToF : Sel(G*) → Sel(F*)`; dualizing gives the final arrow.
The connecting map is not stored independently: it is the transpose of the
reflected-dual localization pairing. -/
structure PoitouTateFiveTerm
    (conditions : PointedConditions k V Q)
    (ReflectedF : Type uRF) (ReflectedG : Type uRG)
    [AddCommGroup ReflectedF] [Module k ReflectedF]
    [AddCommGroup ReflectedG] [Module k ReflectedG] where
  reflectedGToF : ReflectedG →ₗ[k] ReflectedF
  reflectedGToF_injective : Function.Injective reflectedGToF
  reflectedLocalization : ReflectedF →ₗ[k] Module.Dual k Q
  exact_at_pointed : Function.Exact
    conditions.localization reflectedLocalization.flip
  exact_at_reflected : Function.Exact
    reflectedLocalization.flip reflectedGToF.dualMap

namespace PoitouTateFiveTerm

variable {conditions : PointedConditions k V Q}
  (incidence : PoitouTateFiveTerm conditions ReflectedF ReflectedG)

/-- The Poitou--Tate connecting map, defined as the transpose of reflected
localization. -/
def connecting : Q →ₗ[k] Module.Dual k ReflectedF :=
  incidence.reflectedLocalization.flip

/-- The final restriction map on reflected Selmer duals. -/
def reflectedRestriction :
    Module.Dual k ReflectedF →ₗ[k] Module.Dual k ReflectedG :=
  incidence.reflectedGToF.dualMap

/-- The terminal arrow is surjective formally from reversal of the
injective reflected local-condition inclusion. -/
theorem reflectedRestriction_surjective :
    Function.Surjective incidence.reflectedRestriction :=
  LinearMap.dualMap_surjective_of_injective
    incidence.reflectedGToF_injective

/-- The complete five-term shape, including the already-proved exactness at
the relaxed primal term. -/
theorem fiveTerm_exact :
    Function.Exact conditions.strictInclusion conditions.localization ∧
    Function.Exact conditions.localization incidence.connecting ∧
    Function.Exact incidence.connecting incidence.reflectedRestriction :=
  ⟨conditions.exact_at_relaxed, incidence.exact_at_pointed,
    incidence.exact_at_reflected⟩

/-- Rank received by the primal relaxation at the pointed line. -/
noncomputable def primalSteeringGain
    (_incidence : PoitouTateFiveTerm conditions ReflectedF ReflectedG) : ℕ :=
  Module.finrank k (LinearMap.range conditions.localization)

/-- Rank received by the reflected-dual obstruction. -/
noncomputable def reflectedDualObstructionGain : ℕ :=
  Module.finrank k (LinearMap.range incidence.connecting)

/-- **DIMENSION BALANCE.**  Exactness at the pointed local term conserves
its full dimension between primal steering and the reflected-dual
obstruction.  No splitting is chosen. -/
theorem dimension_balance [FiniteDimensional k Q] :
    incidence.primalSteeringGain +
        incidence.reflectedDualObstructionGain = Module.finrank k Q := by
  have hexact :
      LinearMap.range conditions.localization =
        LinearMap.ker incidence.connecting :=
    (LinearMap.exact_iff.mp incidence.exact_at_pointed).symm
  calc
    incidence.primalSteeringGain +
          incidence.reflectedDualObstructionGain =
        Module.finrank k (LinearMap.ker incidence.connecting) +
          Module.finrank k (LinearMap.range incidence.connecting) := by
            rw [primalSteeringGain, reflectedDualObstructionGain, hexact]
    _ = Module.finrank k (LinearMap.range incidence.connecting) +
          Module.finrank k (LinearMap.ker incidence.connecting) :=
      Nat.add_comm _ _
    _ = Module.finrank k Q :=
      incidence.connecting.finrank_range_add_finrank_ker

/-- At a one-dimensional local line, the two gains sum to exactly one. -/
theorem conserved_bit (hQ : Module.finrank k Q = 1)
    [FiniteDimensional k Q] :
    incidence.primalSteeringGain +
        incidence.reflectedDualObstructionGain = 1 := by
  rw [incidence.dimension_balance, hQ]

/-- The only two rank allocations of a one-dimensional local quotient.
This is derived from the dimension coordinate and stores no branch tag. -/
theorem landing_alternatives (hQ : Module.finrank k Q = 1)
    [FiniteDimensional k Q] :
    (incidence.primalSteeringGain = 1 ∧
        incidence.reflectedDualObstructionGain = 0) ∨
      (incidence.primalSteeringGain = 0 ∧
        incidence.reflectedDualObstructionGain = 1) := by
  have hbalance := incidence.conserved_bit hQ
  omega

end PoitouTateFiveTerm

/-! ## The actual conductor-59 seating -/

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  {Delta : Type uDelta} [CommGroup Delta] [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt 59)]
  (rhoQ : QRelaxedSelmerDeltaRepresentation827 K Delta)
  (omega chi : InvolutiveBase.Character (PadicInt 59) Delta)
  (selectedPlace : {v // v ∈ placesOver827 K})

omit [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt 59)] in
/-- The seated reflected eigenspace inherits the same exponent-59 law as
its supported Selmer ambient carrier. -/
theorem qRelaxedReflectedDual827_nsmul_eq_zero
    (y : QRelaxedReflectedDual827 rhoQ omega chi) : 59 • y = 0 := by
  apply Subtype.ext
  exact SelmerEigenspace.p_nsmul_eq_zero y.1

noncomputable local instance instQRelaxedReflectedDual827ModuleZMod :
    Module (ZMod 59) (QRelaxedReflectedDual827 rhoQ omega chi) :=
  AddCommGroup.zmodModule
    (qRelaxedReflectedDual827_nsmul_eq_zero rhoQ omega chi)

/-- The relaxed class/nonpointed-localization observation `G` at 827. -/
noncomputable def relaxedObservation827 :
    QRelaxedSelmerCarrier827 K →ₗ[ZMod 59]
      (ProjectedClassRange827 rhoQ omega chi ×
        NonpointedReadings827 selectedPlace) :=
  jointObservation
    (relaxedClassProjection827 rhoQ omega chi)
    (tameSilence827 rhoQ omega chi selectedPlace)

/-- The strict-at-the-pointed-line observation `F = (G,lambda)`. -/
noncomputable def strictObservation827 :
    QRelaxedSelmerCarrier827 K →ₗ[ZMod 59]
      ((ProjectedClassRange827 rhoQ omega chi ×
          NonpointedReadings827 selectedPlace) × ZMod 59) :=
  strictObservation (relaxedObservation827 rhoQ omega chi selectedPlace)
    (pointedCoordinate827 rhoQ omega chi selectedPlace)

/-- The concrete strict/relaxed incidence on the same q-relaxed carrier. -/
noncomputable def pointedConditions827 :
    PointedConditions (ZMod 59) (QRelaxedSelmerCarrier827 K) (ZMod 59) :=
  { strictF := (strictObservation827 rhoQ omega chi selectedPlace).ker
    relaxedG := K_T
      (relaxedClassProjection827 rhoQ omega chi)
      (tameSilence827 rhoQ omega chi selectedPlace)
    strict_le_relaxed := by
      intro v hv
      rw [strictObservation827, strictObservation, LinearMap.ker_prod] at hv
      simpa [relaxedObservation827, jointObservation, K_T] using hv.1
    localization :=
      pointedConormalRestriction827 rhoQ omega chi selectedPlace
    exact_at_relaxed := by
      rw [LinearMap.exact_iff]
      ext x
      constructor
      · intro hx
        rw [LinearMap.mem_ker] at hx
        change pointedCoordinate827 rhoQ omega chi selectedPlace x.1 = 0 at hx
        refine ⟨⟨x.1, ?_⟩, rfl⟩
        rw [strictObservation827, strictObservation, LinearMap.ker_prod]
        refine ⟨?_, LinearMap.mem_ker.mpr hx⟩
        change relaxedObservation827 rhoQ omega chi selectedPlace x.1 = 0
        apply Prod.ext
        · change relaxedClassProjection827 rhoQ omega chi x.1 = 0
          exact LinearMap.mem_ker.mp x.property.1
        · change tameSilence827 rhoQ omega chi selectedPlace x.1 = 0
          exact LinearMap.mem_ker.mp x.property.2
      · rintro ⟨y, rfl⟩
        rw [LinearMap.mem_ker]
        change pointedCoordinate827 rhoQ omega chi selectedPlace y.1 = 0
        have hy : strictObservation827 rhoQ omega chi selectedPlace y.1 = 0 :=
          LinearMap.mem_ker.mp y.property
        have hsnd := congrArg Prod.snd hy
        change pointedCoordinate827 rhoQ omega chi selectedPlace y.1 = 0 at hsnd
        exact hsnd }

/-- The actual selected localization on the seated reflected-character
q-relaxed Selmer carrier. -/
noncomputable def reflectedPointedLocalization827 :
    QRelaxedReflectedDual827 rhoQ omega chi →ₗ[ZMod 59] ZMod 59 :=
  (qLocalizationCoordinate827 rhoQ omega chi selectedPlace).toZModLinearMap 59

/-- The reflected condition dual to primal relaxation: selected localization
is strict, so it is the kernel inside the q-relaxed reflected carrier. -/
abbrev ReflectedG827 :=
  LinearMap.ker
    (reflectedPointedLocalization827 rhoQ omega chi selectedPlace)

/-- The reversed inclusion `Sel(G*) → Sel(F*)`. -/
def reflectedGToF827 :
    ReflectedG827 rhoQ omega chi selectedPlace →ₗ[ZMod 59]
      QRelaxedReflectedDual827 rhoQ omega chi :=
  (ReflectedG827 rhoQ omega chi selectedPlace).subtype

/-- Multiplication identifies the one-dimensional local coordinate with its
dual.  Composing it with the actual reflected localization produces the
seated local pairing whose transpose is the Poitou--Tate boundary. -/
noncomputable def reflectedCoordinatePairing827 :
    QRelaxedReflectedDual827 rhoQ omega chi →ₗ[ZMod 59]
      Module.Dual (ZMod 59) (ZMod 59) :=
  (LinearMap.mul (ZMod 59) (ZMod 59)).comp
    (reflectedPointedLocalization827 rhoQ omega chi selectedPlace)

/-- **CLASS-FIELD-THEORY INPUT AT 827.**  This is the exact five-term
incidence with every available primal and reflected localization map fixed
to its seated implementation.  Only its Poitou--Tate exactness laws are
fields; no branch or chosen element is stored. -/
structure PointedTateIncidence827 : Prop where
  exact_at_pointed : Function.Exact
    (pointedConditions827 rhoQ omega chi selectedPlace).localization
    (reflectedCoordinatePairing827 rhoQ omega chi selectedPlace).flip
  exact_at_reflected : Function.Exact
    (reflectedCoordinatePairing827 rhoQ omega chi selectedPlace).flip
    (reflectedGToF827 rhoQ omega chi selectedPlace).dualMap

namespace PointedTateIncidence827

variable {rhoQ omega chi selectedPlace}

/-- Forgetting the 827 names gives exactly the generic five-term interface. -/
def toPoitouTateFiveTerm
    (incidence : PointedTateIncidence827 rhoQ omega chi selectedPlace) :
    PoitouTateFiveTerm
      (pointedConditions827 rhoQ omega chi selectedPlace)
      (QRelaxedReflectedDual827 rhoQ omega chi)
      (ReflectedG827 rhoQ omega chi selectedPlace) where
  reflectedGToF := reflectedGToF827 rhoQ omega chi selectedPlace
  reflectedGToF_injective := Submodule.subtype_injective _
  reflectedLocalization :=
    reflectedCoordinatePairing827 rhoQ omega chi selectedPlace
  exact_at_pointed := incidence.exact_at_pointed
  exact_at_reflected := incidence.exact_at_reflected

/-- The primal arrow is definitionally the retained pointed conormal
restriction from W2. -/
theorem primalLocalization_eq_pointedConormalRestriction
    (_incidence : PointedTateIncidence827 rhoQ omega chi selectedPlace) :
    (pointedConditions827 rhoQ omega chi selectedPlace).localization =
      pointedConormalRestriction827 rhoQ omega chi selectedPlace :=
  rfl

/-- The reflected connecting arrow evaluates through the actual seated
reflected-character localization coordinate. -/
@[simp]
theorem connecting_apply
    (incidence : PointedTateIncidence827 rhoQ omega chi selectedPlace)
    (q : ZMod 59) (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    incidence.toPoitouTateFiveTerm.connecting q y =
      reflectedPointedLocalization827 rhoQ omega chi selectedPlace y * q :=
  rfl

/-- The pointed local quotient is one-dimensional. -/
theorem q827_finrank : Module.finrank (ZMod 59) (ZMod 59) = 1 := by
  simp

/-- **CONSERVED BIT AT 827.**  The primal steering gain plus the reflected
dual obstruction gain is exactly one. -/
theorem conserved_bit
    (incidence : PointedTateIncidence827 rhoQ omega chi selectedPlace) :
    incidence.toPoitouTateFiveTerm.primalSteeringGain +
        incidence.toPoitouTateFiveTerm.reflectedDualObstructionGain = 1 :=
  incidence.toPoitouTateFiveTerm.conserved_bit q827_finrank

/-- Vanishing of the retained conormal coordinate is exactly zero primal
gain. -/
theorem conormalClass_eq_zero_iff_primalGain_eq_zero
    (incidence : PointedTateIncidence827 rhoQ omega chi selectedPlace) :
    pointedConormalClass827 rhoQ omega chi selectedPlace = 0 ↔
      incidence.toPoitouTateFiveTerm.primalSteeringGain = 0 := by
  have hrestriction :
      pointedConormalRestriction827 rhoQ omega chi selectedPlace = 0 ↔
        FixedAttention
          (relaxedClassProjection827 rhoQ omega chi)
          (tameSilence827 rhoQ omega chi selectedPlace)
          (pointedCoordinate827 rhoQ omega chi selectedPlace) :=
    focusConormalRestriction_eq_zero_iff_fixed _ _ _
  have hclassRestriction :
      pointedConormalClass827 rhoQ omega chi selectedPlace = 0 ↔
        pointedConormalRestriction827 rhoQ omega chi selectedPlace = 0 :=
    (pointedConormalClass827_eq_zero_iff_fixed _ _ _ _).trans
      hrestriction.symm
  rw [hclassRestriction]
  change
    pointedConormalRestriction827 rhoQ omega chi selectedPlace = 0 ↔
      Module.finrank (ZMod 59)
        (LinearMap.range
          (pointedConditions827 rhoQ omega chi selectedPlace).localization) = 0
  rw [incidence.primalLocalization_eq_pointedConormalRestriction,
    Submodule.finrank_eq_zero]
  exact LinearMap.range_eq_bot.symm

/-- If the reflected dual receives the conserved dimension, the old shadow
is the fixed future. -/
theorem reflectedGain_eq_one_iff_fixed
    (incidence : PointedTateIncidence827 rhoQ omega chi selectedPlace) :
    incidence.toPoitouTateFiveTerm.reflectedDualObstructionGain = 1 ↔
      FixedAttention
        (relaxedClassProjection827 rhoQ omega chi)
        (tameSilence827 rhoQ omega chi selectedPlace)
        (pointedCoordinate827 rhoQ omega chi selectedPlace) := by
  have hbalance := incidence.conserved_bit
  rw [← pointedConormalClass827_eq_zero_iff_fixed]
  rw [incidence.conormalClass_eq_zero_iff_primalGain_eq_zero]
  omega

/-- If the primal side receives the conserved dimension, the old shadow is
the steerable future. -/
theorem primalGain_eq_one_iff_transverse
    (incidence : PointedTateIncidence827 rhoQ omega chi selectedPlace) :
    incidence.toPoitouTateFiveTerm.primalSteeringGain = 1 ↔
      Nonempty
        (TransverseDirection
          (relaxedClassProjection827 rhoQ omega chi)
          (tameSilence827 rhoQ omega chi selectedPlace)
          (pointedCoordinate827 rhoQ omega chi selectedPlace)) := by
  have hbalance := incidence.conserved_bit
  rw [← pointedConormalClass827_ne_zero_iff_transverse]
  have hzero := incidence.conormalClass_eq_zero_iff_primalGain_eq_zero
  constructor
  · intro hprimal hclass
    have : incidence.toPoitouTateFiveTerm.primalSteeringGain = 0 :=
      hzero.mp hclass
    omega
  · intro hclass
    have hne : incidence.toPoitouTateFiveTerm.primalSteeringGain ≠ 0 := by
      intro hprimal
      exact hclass (hzero.mpr hprimal)
    omega

/-- The two already-compiled futures, indexed by the rank coordinate rather
than by an independently supplied Boolean. -/
theorem compiled_future_alternatives
    (incidence : PointedTateIncidence827 rhoQ omega chi selectedPlace) :
    (incidence.toPoitouTateFiveTerm.primalSteeringGain = 1 ∧
        Nonempty
          (TransverseDirection
            (relaxedClassProjection827 rhoQ omega chi)
            (tameSilence827 rhoQ omega chi selectedPlace)
            (pointedCoordinate827 rhoQ omega chi selectedPlace))) ∨
      (incidence.toPoitouTateFiveTerm.reflectedDualObstructionGain = 1 ∧
        FixedAttention
          (relaxedClassProjection827 rhoQ omega chi)
          (tameSilence827 rhoQ omega chi selectedPlace)
          (pointedCoordinate827 rhoQ omega chi selectedPlace)) := by
  rcases incidence.toPoitouTateFiveTerm.landing_alternatives q827_finrank with
      hprimal | hreflected
  · exact Or.inl ⟨hprimal.1,
      incidence.primalGain_eq_one_iff_transverse.mp hprimal.1⟩
  · exact Or.inr ⟨hreflected.2,
      incidence.reflectedGain_eq_one_iff_fixed.mp hreflected.2⟩

end PointedTateIncidence827

/-! ## The conditional Fourier landing -/

section FourierLanding

variable {K59 : Type} [Field K59] [NumberField K59]
  [IsCyclotomicExtension {59} ℚ K59]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  (rhoQ59 : QRelaxedSelmerDeltaRepresentation827 K59 GaloisIndex59)
  (omega59 chi59 :
    InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
  (selected59 : Place827 K59)

/-- W1's missing equivariant seating law, together with the W3
Poitou--Tate incidence, puts the conserved dimension on the reflected-dual
side.  Both arithmetic interfaces remain explicit premises. -/
theorem reflectedGain_eq_one_of_fourierSeating
    (incidence :
      PointedTateIncidence827 rhoQ59 omega59 chi59 selected59)
    (seating :
      QLocalizationEquivariance827 rhoQ59 omega59 chi59 selected59) :
    incidence.toPoitouTateFiveTerm.reflectedDualObstructionGain = 1 :=
  (incidence.reflectedGain_eq_one_iff_fixed).2
    (fixedAttention_of_fourierSeating
      rhoQ59 omega59 chi59 selected59 seating)

end FourierLanding

end Fermat.FiftyNine.Conservation.PointedTateIncidence
