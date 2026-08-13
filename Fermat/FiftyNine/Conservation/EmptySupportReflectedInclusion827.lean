/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The canonical empty-support inclusion on reflected eigenspaces

The inclusion from Mathlib's empty-support Selmer group into a supported
Selmer group is canonical and injective.  To restrict it to supplied
character eigenspaces, the only arithmetic input needed is that the image of
the old eigenspace lands in the new eigenspace.  A stronger, natural
action-compatibility interface implies this landing condition.

Once landing is known, linearity over the integral 59-adic group algebra is
formal: both source and target have the same character.  No equivalence,
section, complement, or splitting of the strict and relaxed carriers is used.
-/
import Fermat.FiftyNine.Conservation.SplitPrimeFourier827
import Mathlib.RepresentationTheory.Intertwining

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

universe uR uK uDelta

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

/-! ## Generic support inclusion at 59 -/

variable {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {Delta : Type uDelta} [CommGroup Delta]
  {S : Set (IsDedekindDomain.HeightOneSpectrum R)}

/-- The canonical empty-support inclusion, promoted to a `PadicInt 59`-linear
map.  Both coefficient actions factor through `ZMod 59`, so additivity is
already enough for this promotion. -/
def emptySupportInclusionPadic :
    SelmerCarrier R K 59 →ₗ[PadicInt 59] SelmerCarrierAt R K S 59 where
  toFun := emptySupportInclusion (R := R) (K := K) (p := 59) (S := S)
  map_add' := map_add _
  map_smul' a x := by
    change emptySupportInclusion (R := R) (K := K) (p := 59) (S := S)
        (PadicInt.toZMod a • x) =
      PadicInt.toZMod a •
        emptySupportInclusion (R := R) (K := K) (p := 59) (S := S) x
    exact ZMod.map_smul
      (emptySupportInclusion (R := R) (K := K) (p := 59) (S := S))
      (PadicInt.toZMod a) x

/-- The canonical support inclusion loses no Selmer class. -/
theorem emptySupportInclusionPadic_injective :
    Function.Injective
      (emptySupportInclusionPadic (R := R) (K := K) (S := S)) := by
  intro x y hxy
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun z ↦ (Additive.toMul z).1) hxy

/-- The exact minimal compatibility needed to restrict the canonical support
inclusion to one supplied character eigenspace. -/
structure EmptySupportEigenspaceLanding
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
      (Delta := Delta))
    (rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := 59)
      (Delta := Delta) S)
    (eta : InvolutiveBase.Character (PadicInt 59) Delta) : Prop where
  map_mem : ∀ x : SelmerChi rho eta,
    emptySupportInclusion (R := R) (K := K) (p := 59) (S := S) x.1 ∈
      characterEigenspaceAt rhoS eta

/-- The natural stronger arithmetic interface: the two supplied actions
agree along the canonical inclusion on the complete empty-support carrier. -/
structure EmptySupportActionCompatibility
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
      (Delta := Delta))
    (rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := 59)
      (Delta := Delta) S) : Prop where
  inclusion_intertwines : ∀ delta x,
    rhoS delta
        (emptySupportInclusionPadic (R := R) (K := K) (S := S) x) =
      emptySupportInclusionPadic (R := R) (K := K) (S := S) (rho delta x)

namespace EmptySupportActionCompatibility

variable
  {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
    (Delta := Delta)}
  {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := 59)
    (Delta := Delta) S}

/-- Ambient action compatibility implies landing for every character. -/
def toEigenspaceLanding
    (compatibility : EmptySupportActionCompatibility rho rhoS)
    (eta : InvolutiveBase.Character (PadicInt 59) Delta) :
    EmptySupportEigenspaceLanding rho rhoS eta where
  map_mem := by
    intro x
    rw [mem_characterEigenspaceAt_iff]
    intro delta
    change rhoS delta
        (emptySupportInclusionPadic (R := R) (K := K) (S := S) x.1) =
      (eta delta : PadicInt 59) •
        emptySupportInclusionPadic (R := R) (K := K) (S := S) x.1
    rw [compatibility.inclusion_intertwines]
    rw [(mem_characterEigenspace_iff rho eta x.1).mp x.property delta]
    exact map_smul
      (emptySupportInclusionPadic (R := R) (K := K) (S := S))
      (eta delta : PadicInt 59) x.1

end EmptySupportActionCompatibility

/-- The canonical inclusion restricted to a landed eigenspace, first as a
`PadicInt 59`-linear map. -/
def emptySupportEigenspaceInclusionPadic
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := 59)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt 59) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta) :
    SelmerChi rho eta →ₗ[PadicInt 59] SelmerChiAt rhoS eta :=
  LinearMap.codRestrict (characterEigenspaceAt rhoS eta)
    (emptySupportInclusionPadic (R := R) (K := K) (S := S) |>.comp
      (characterEigenspace rho eta).subtype)
    landing.map_mem

@[simp]
theorem emptySupportEigenspaceInclusionPadic_apply
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := 59)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt 59) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta)
    (x : SelmerChi rho eta) :
    (emptySupportEigenspaceInclusionPadic landing x :
        SelmerCarrierAt R K S 59) =
      emptySupportInclusion (R := R) (K := K) (p := 59) (S := S) x.1 :=
  rfl

/-- Landing makes the restricted inclusion intertwine the two restricted
representations. -/
theorem emptySupportEigenspaceInclusionPadic_intertwines
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := 59)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt 59) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta)
    (delta : Delta) (x : SelmerChi rho eta) :
    emptySupportEigenspaceInclusionPadic landing
        (characterEigenspaceRepresentation rho eta delta x) =
      characterEigenspaceRepresentationAt rhoS eta delta
        (emptySupportEigenspaceInclusionPadic landing x) := by
  apply Subtype.ext
  rw [show characterEigenspaceRepresentation rho eta delta x =
      (eta delta : PadicInt 59) • x by
    apply Subtype.ext
    exact (mem_characterEigenspace_iff rho eta x.1).mp x.property delta]
  rw [map_smul]
  change (eta delta : PadicInt 59) •
      (emptySupportEigenspaceInclusionPadic landing x).1 =
    rhoS delta (emptySupportEigenspaceInclusionPadic landing x).1
  exact ((mem_characterEigenspaceAt_iff rhoS eta
    (emptySupportEigenspaceInclusionPadic landing x).1).mp
      (emptySupportEigenspaceInclusionPadic landing x).property delta).symm

/-- The canonical landed inclusion, linear over the complete integral
59-adic group algebra. -/
noncomputable def emptySupportEigenspaceInclusion
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := 59)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt 59) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta) :
    SelmerChi rho eta →ₗ[IntegralPadicGroupAlgebra 59 Delta]
      SelmerChiAt rhoS eta := by
  let f : Representation.IntertwiningMap
      (characterEigenspaceRepresentation rho eta)
      (characterEigenspaceRepresentationAt rhoS eta) :=
    (emptySupportEigenspaceInclusionPadic landing).intertwiningMap_of_isIntertwiningMap
      (characterEigenspaceRepresentation rho eta)
      (characterEigenspaceRepresentationAt rhoS eta)
      (emptySupportEigenspaceInclusionPadic_intertwines landing)
  exact Representation.IntertwiningMap.equivLinearMapAsModule
    (characterEigenspaceRepresentation rho eta)
    (characterEigenspaceRepresentationAt rhoS eta) f

@[simp]
theorem emptySupportEigenspaceInclusion_apply
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := 59)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt 59) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta)
    (x : SelmerChi rho eta) :
    (emptySupportEigenspaceInclusion landing x : SelmerCarrierAt R K S 59) =
      emptySupportInclusion (R := R) (K := K) (p := 59) (S := S) x.1 :=
  rfl

/-- The canonical landed eigenspace inclusion is injective. -/
theorem emptySupportEigenspaceInclusion_injective
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := 59)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt 59) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta) :
    Function.Injective (emptySupportEigenspaceInclusion landing) := by
  intro x y hxy
  apply Subtype.ext
  apply emptySupportInclusionPadic_injective (R := R) (K := K) (S := S)
  exact congrArg Subtype.val hxy

/-- The strict and relaxed inclusions expose the identical Kummer quotient
class. -/
@[simp]
theorem toKummerQuotientAt_emptySupportEigenspaceInclusion
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := 59)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt 59) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta)
    (x : SelmerChi rho eta) :
    toKummerQuotientAt (emptySupportEigenspaceInclusion landing x) =
      toKummerQuotient x :=
  rfl

/-- Additive Kummer-class calibration along the canonical landed inclusion. -/
@[simp]
theorem toKummerClassAt_emptySupportEigenspaceInclusion
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := 59)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt 59) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta)
    (x : SelmerChi rho eta) :
    toKummerClassAt (emptySupportEigenspaceInclusion landing x) =
      toKummerClass x :=
  rfl

/-! ## The reflected 827 specialization -/

variable {K59 : Type uK} [Field K59] [NumberField K59]
  (rho : SelmerDeltaRepresentation (R := 𝓞 K59) (K := K59) (p := 59)
    (Delta := GaloisIndex59))
  (rhoQ : QRelaxedSelmerDeltaRepresentation827 K59 GaloisIndex59)
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

/-- Minimal landing core for the old reflected eigenspace at auxiliary
support 827. -/
abbrev ReflectedEmptySupportLanding827 :=
  EmptySupportEigenspaceLanding rho rhoQ
    (InvolutiveBase.reflectedCharacter omega chi)

/-- Ambient action compatibility at auxiliary support 827. -/
abbrev EmptySupportActionCompatibility827 :=
  EmptySupportActionCompatibility rho rhoQ

/-- Ambient compatibility gives the reflected landing receipt at 827. -/
def EmptySupportActionCompatibility827.toReflectedLanding
    (compatibility : EmptySupportActionCompatibility827 rho rhoQ) :
    ReflectedEmptySupportLanding827 rho rhoQ omega chi :=
  compatibility.toEigenspaceLanding
    (InvolutiveBase.reflectedCharacter omega chi)

/-- The canonical integral-group-algebra-linear inclusion of the concrete
old reflected dual into the q-relaxed reflected dual. -/
noncomputable def oldReflectedToQRelaxed827
    (landing : ReflectedEmptySupportLanding827 rho rhoQ omega chi) :
    DOmegaSelmerChiStar rho omega chi
      →ₗ[IntegralPadicGroupAlgebra 59 GaloisIndex59]
      QRelaxedReflectedDual827 rhoQ omega chi :=
  emptySupportEigenspaceInclusion landing

/-- The canonical reflected inclusion is injective. -/
theorem oldReflectedToQRelaxed827_injective
    (landing : ReflectedEmptySupportLanding827 rho rhoQ omega chi) :
    Function.Injective (oldReflectedToQRelaxed827 rho rhoQ omega chi landing) :=
  emptySupportEigenspaceInclusion_injective landing

/-- The q-relaxed Kummer class of an included old reflected class is the
original strict Kummer class. -/
@[simp]
theorem toKummerClassAt_oldReflectedToQRelaxed827
    (landing : ReflectedEmptySupportLanding827 rho rhoQ omega chi)
    (y : DOmegaSelmerChiStar rho omega chi) :
    toKummerClassAt
        (oldReflectedToQRelaxed827 rho rhoQ omega chi landing y) =
      toKummerClass y :=
  toKummerClassAt_emptySupportEigenspaceInclusion landing y

end Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827
