/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Prime-generic empty-support inclusion on Selmer eigenspaces

For every prime `p`, the canonical inclusion from Mathlib's empty-support
Selmer group into an arbitrary supported Selmer group is linear over
`PadicInt p` and injective.  Whenever two supplied actions agree along that
literal inclusion, it restricts to every character eigenspace and is linear
over the integral `p`-adic group algebra.

The constructions below preserve Mathlib's actual empty-support inclusion.
No section, complement, splitting, or replacement carrier is introduced.
-/
import Fermat.Experiments.Conservation.SelmerEigenspace
import Mathlib.RepresentationTheory.Intertwining

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.SelmerEigenspace

universe uR uK uDelta

variable {p : ℕ} [Fact p.Prime]
variable {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {Delta : Type uDelta} [CommGroup Delta]
  {S : Set (IsDedekindDomain.HeightOneSpectrum R)}

/-- The canonical empty-support inclusion, promoted to a `PadicInt p`-linear
map.  Both coefficient actions factor through `ZMod p`, so additivity is
already enough for this promotion. -/
def emptySupportInclusionPadic :
    SelmerCarrier R K p →ₗ[PadicInt p] SelmerCarrierAt R K S p where
  toFun := emptySupportInclusion (R := R) (K := K) (p := p) (S := S)
  map_add' := map_add _
  map_smul' a x := by
    change emptySupportInclusion (R := R) (K := K) (p := p) (S := S)
        (PadicInt.toZMod a • x) =
      PadicInt.toZMod a •
        emptySupportInclusion (R := R) (K := K) (p := p) (S := S) x
    exact ZMod.map_smul
      (emptySupportInclusion (R := R) (K := K) (p := p) (S := S))
      (PadicInt.toZMod a) x

/-- The canonical support inclusion loses no Selmer class. -/
theorem emptySupportInclusionPadic_injective :
    Function.Injective
      (emptySupportInclusionPadic (p := p) (R := R) (K := K) (S := S)) := by
  intro x y hxy
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun z ↦ (Additive.toMul z).1) hxy

/-- The exact minimal compatibility needed to restrict the canonical support
inclusion to one supplied character eigenspace. -/
structure EmptySupportEigenspaceLanding
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta))
    (rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S)
    (eta : InvolutiveBase.Character (PadicInt p) Delta) : Prop where
  map_mem : ∀ x : SelmerChi rho eta,
    emptySupportInclusion (R := R) (K := K) (p := p) (S := S) x.1 ∈
      characterEigenspaceAt rhoS eta

/-- The natural stronger arithmetic interface: the two supplied actions
agree along the canonical inclusion on the complete empty-support carrier. -/
structure EmptySupportActionCompatibility
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta))
    (rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S) : Prop where
  inclusion_intertwines : ∀ delta x,
    rhoS delta
        (emptySupportInclusionPadic
          (p := p) (R := R) (K := K) (S := S) x) =
      emptySupportInclusionPadic
        (p := p) (R := R) (K := K) (S := S) (rho delta x)

namespace EmptySupportActionCompatibility

variable
  {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
    (Delta := Delta)}
  {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
    (Delta := Delta) S}

/-- Ambient action compatibility implies landing for every character. -/
def toEigenspaceLanding
    (compatibility : EmptySupportActionCompatibility rho rhoS)
    (eta : InvolutiveBase.Character (PadicInt p) Delta) :
    EmptySupportEigenspaceLanding rho rhoS eta where
  map_mem := by
    intro x
    rw [mem_characterEigenspaceAt_iff]
    intro delta
    change rhoS delta
        (emptySupportInclusionPadic
          (p := p) (R := R) (K := K) (S := S) x.1) =
      (eta delta : PadicInt p) •
        emptySupportInclusionPadic
          (p := p) (R := R) (K := K) (S := S) x.1
    rw [compatibility.inclusion_intertwines]
    rw [(mem_characterEigenspace_iff rho eta x.1).mp x.property delta]
    exact map_smul
      (emptySupportInclusionPadic
        (p := p) (R := R) (K := K) (S := S))
      (eta delta : PadicInt p) x.1

end EmptySupportActionCompatibility

/-- The canonical inclusion restricted to a landed eigenspace, first as a
`PadicInt p`-linear map. -/
def emptySupportEigenspaceInclusionPadic
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta) :
    SelmerChi rho eta →ₗ[PadicInt p] SelmerChiAt rhoS eta :=
  LinearMap.codRestrict (characterEigenspaceAt rhoS eta)
    (emptySupportInclusionPadic
      (p := p) (R := R) (K := K) (S := S) |>.comp
      (characterEigenspace rho eta).subtype)
    landing.map_mem

@[simp]
theorem emptySupportEigenspaceInclusionPadic_apply
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta)
    (x : SelmerChi rho eta) :
    (emptySupportEigenspaceInclusionPadic landing x :
        SelmerCarrierAt R K S p) =
      emptySupportInclusion (R := R) (K := K) (p := p) (S := S) x.1 :=
  rfl

/-- Landing makes the restricted inclusion intertwine the two restricted
representations. -/
theorem emptySupportEigenspaceInclusionPadic_intertwines
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta)
    (delta : Delta) (x : SelmerChi rho eta) :
    emptySupportEigenspaceInclusionPadic landing
        (characterEigenspaceRepresentation rho eta delta x) =
      characterEigenspaceRepresentationAt rhoS eta delta
        (emptySupportEigenspaceInclusionPadic landing x) := by
  apply Subtype.ext
  rw [show characterEigenspaceRepresentation rho eta delta x =
      (eta delta : PadicInt p) • x by
    apply Subtype.ext
    exact (mem_characterEigenspace_iff rho eta x.1).mp x.property delta]
  rw [map_smul]
  change (eta delta : PadicInt p) •
      (emptySupportEigenspaceInclusionPadic landing x).1 =
    rhoS delta (emptySupportEigenspaceInclusionPadic landing x).1
  exact ((mem_characterEigenspaceAt_iff rhoS eta
    (emptySupportEigenspaceInclusionPadic landing x).1).mp
      (emptySupportEigenspaceInclusionPadic landing x).property delta).symm

/-- The canonical landed inclusion, linear over the complete integral
`p`-adic group algebra. -/
noncomputable def emptySupportEigenspaceInclusion
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta) :
    SelmerChi rho eta →ₗ[IntegralPadicGroupAlgebra p Delta]
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
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta)
    (x : SelmerChi rho eta) :
    (emptySupportEigenspaceInclusion landing x : SelmerCarrierAt R K S p) =
      emptySupportInclusion (R := R) (K := K) (p := p) (S := S) x.1 :=
  rfl

/-- The canonical landed eigenspace inclusion is injective. -/
theorem emptySupportEigenspaceInclusion_injective
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta) :
    Function.Injective (emptySupportEigenspaceInclusion landing) := by
  intro x y hxy
  apply Subtype.ext
  apply emptySupportInclusionPadic_injective
    (p := p) (R := R) (K := K) (S := S)
  exact congrArg Subtype.val hxy

/-- The strict and relaxed inclusions expose the identical Kummer quotient
class. -/
@[simp]
theorem toKummerQuotientAt_emptySupportEigenspaceInclusion
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta)
    (x : SelmerChi rho eta) :
    toKummerQuotientAt (emptySupportEigenspaceInclusion landing x) =
      toKummerQuotient x :=
  rfl

/-- Additive Kummer-class calibration along the canonical landed inclusion. -/
@[simp]
theorem toKummerClassAt_emptySupportEigenspaceInclusion
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := p)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := p)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt p) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta)
    (x : SelmerChi rho eta) :
    toKummerClassAt (emptySupportEigenspaceInclusion landing x) =
      toKummerClass x :=
  rfl

end Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion
