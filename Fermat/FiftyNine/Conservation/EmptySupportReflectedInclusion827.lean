/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The 59/827 adapter for empty-support inclusion on reflected eigenspaces

The prime-generic inclusion, injectivity, action compatibility, eigenspace
restriction, and Kummer readbacks live in
`Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion`.  This file keeps
their established `p = 59` names as transparent compatibility wrappers.

Only the reflected specialization to the actual support above 827 remains
local.  No equivalence, section, complement, or splitting of the strict and
relaxed carriers is used.
-/
import Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion
import Fermat.FiftyNine.Conservation.SplitPrimeFourier827

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

/-! ## Prime-generic support inclusion specialized at 59 -/

variable {R : Type uR} [CommRing R] [IsDedekindDomain R]
  {K : Type uK} [Field K] [Algebra R K] [IsFractionRing R K]
  {Delta : Type uDelta} [CommGroup Delta]
  {S : Set (IsDedekindDomain.HeightOneSpectrum R)}

/-- The prime-generic canonical empty-support inclusion at `p = 59`. -/
def emptySupportInclusionPadic :
    SelmerCarrier R K 59 →ₗ[PadicInt 59] SelmerCarrierAt R K S 59 :=
  Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion.emptySupportInclusionPadic
    (p := 59) (R := R) (K := K) (S := S)

/-- The canonical support inclusion loses no Selmer class. -/
theorem emptySupportInclusionPadic_injective :
    Function.Injective
      (emptySupportInclusionPadic (R := R) (K := K) (S := S)) :=
  Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion.emptySupportInclusionPadic_injective
    (p := 59) (R := R) (K := K) (S := S)

/-- The exact minimal compatibility needed to restrict the canonical support
inclusion to one supplied character eigenspace. -/
abbrev EmptySupportEigenspaceLanding
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
      (Delta := Delta))
    (rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := 59)
      (Delta := Delta) S)
    (eta : InvolutiveBase.Character (PadicInt 59) Delta) : Prop :=
  Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion.EmptySupportEigenspaceLanding
    rho rhoS eta

/-- The natural stronger arithmetic interface: the two supplied actions
agree along the canonical inclusion on the complete empty-support carrier. -/
abbrev EmptySupportActionCompatibility
    (rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
      (Delta := Delta))
    (rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := 59)
      (Delta := Delta) S) : Prop :=
  Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion.EmptySupportActionCompatibility
    rho rhoS

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
    EmptySupportEigenspaceLanding rho rhoS eta :=
  Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion.EmptySupportActionCompatibility.toEigenspaceLanding
    compatibility eta

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
  Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion.emptySupportEigenspaceInclusionPadic
    landing

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
  Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion.emptySupportEigenspaceInclusionPadic_apply
    landing x

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
        (emptySupportEigenspaceInclusionPadic landing x) :=
  Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion.emptySupportEigenspaceInclusionPadic_intertwines
    landing delta x

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
      SelmerChiAt rhoS eta :=
  Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion.emptySupportEigenspaceInclusion
    landing

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
  Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion.emptySupportEigenspaceInclusion_apply
    landing x

/-- The canonical landed eigenspace inclusion is injective. -/
theorem emptySupportEigenspaceInclusion_injective
    {rho : SelmerDeltaRepresentation (R := R) (K := K) (p := 59)
      (Delta := Delta)}
    {rhoS : SelmerDeltaRepresentationAt (R := R) (K := K) (p := 59)
      (Delta := Delta) S}
    {eta : InvolutiveBase.Character (PadicInt 59) Delta}
    (landing : EmptySupportEigenspaceLanding rho rhoS eta) :
    Function.Injective (emptySupportEigenspaceInclusion landing) :=
  Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion.emptySupportEigenspaceInclusion_injective
    landing

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
  Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion.toKummerQuotientAt_emptySupportEigenspaceInclusion
    landing x

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
  Fermat.Conservation.PrimeEmptySupportEigenspaceInclusion.toKummerClassAt_emptySupportEigenspaceInclusion
    landing x

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
