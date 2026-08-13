/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Ulam W0: freeze the reflected/wild carrier boundary

The pointed Poitou--Tate architecture contains the localization covector
`reflectedBoundaryFunctional827` on the q-relaxed reflected carrier.  It is
not a reflected class `y*`, nor the pairing functional on `H_FLT` obtained by
fixing such a class.  Thus the Ulam STOP condition fires despite the genuine
map beneath W4's allocation count.

This file names exactly the missing W1 data without constructing it.  First,
the existing wild pairing must extend to the q-relaxed carrier and agree on
an equivariantly included old carrier.  Second, that carrier needs a class
`y*` normalized by its 827 localization.  Only then does fixing `y*` produce
the correctly variant functional `x ↦ ⟨x,y*⟩` on `H_FLT`.

The normalization value and every local Tate-pairing value remain strictly
separate.  No inhabitant, pairing vanishing, comparison theorem, reciprocity
law, relation (7a), or Lane-1 realization is fabricated.
-/
import Fermat.FiftyNine.Conservation.PointedTateIncidence
import Fermat.FiftyNine.Conservation.TateBridge

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.UlamTypeFreeze

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.PointedTateIncidence
open Fermat.FiftyNine.Conservation.TateBridge

universe uDelta uPlace uSelmer uDual

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  {Delta : Type uDelta} [CommGroup Delta] [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt 59)]
  (rhoQ : QRelaxedSelmerDeltaRepresentation827 K Delta)
  (omega chi : InvolutiveBase.Character (PadicInt 59) Delta)
  {Place : Type uPlace} {SelmerChi : Type uSelmer}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChi]
  {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra 59 Delta) DOmegaSelmerChiStar]
  (distinguishedPlace : Place)
  (wild : WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
    (Place := Place) (SelmerChi := SelmerChi)
    (DOmegaSelmerChiStar := DOmegaSelmerChiStar) distinguishedPlace)

/-- **W0 TYPED CARRIER OBSTRUCTION.**  A q-relaxed extension of the existing
wild pairing, compatible along an equivariant inclusion of the old reflected
carrier.  This does not identify the strict and relaxed carriers by an
equivalence and does not manufacture new pairing values. -/
structure ReflectedWildCarrierExtension827 where
  oldToQRelaxed :
    DOmegaSelmerChiStar →ₗ[IntegralPadicGroupAlgebra 59 Delta]
      QRelaxedReflectedDual827 rhoQ omega chi
  oldToQRelaxed_injective : Function.Injective oldToQRelaxed
  qRelaxedWild :
    WildLocalInterface (Delta := Delta) (omega := omega) (chi := chi)
      (Place := Place) (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := QRelaxedReflectedDual827 rhoQ omega chi)
      distinguishedPlace
  reading_compatibility : ∀ x y,
    qRelaxedWild.reading x (oldToQRelaxed y) = wild.reading x y

namespace ReflectedWildCarrierExtension827

variable {rhoQ omega chi distinguishedPlace wild}

omit [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt 59)] in
/-- The q-relaxed extension agrees with the existing arithmetic reading on
the included old reflected carrier. -/
theorem qRelaxedWild_reading_oldToQRelaxed
    (extension : ReflectedWildCarrierExtension827
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      rhoQ omega chi distinguishedPlace wild)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) :
    extension.qRelaxedWild.reading x (extension.oldToQRelaxed y) =
      wild.reading x y :=
  extension.reading_compatibility x y

end ReflectedWildCarrierExtension827

variable
  (selectedPlace : {v // v ∈ placesOver827 K})

/-- **THE W1 WITNESS SHAPE.**  A reflected q-relaxed class with normalization
at the selected 827 place.  This structure is an uninhabited obstruction
probe, not a Lane-1 construction. -/
structure NormalizedReflectedClass827
    (extension : ReflectedWildCarrierExtension827
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      rhoQ omega chi distinguishedPlace wild) where
  yStar : QRelaxedReflectedDual827 rhoQ omega chi
  normalization :
    reflectedBoundaryFunctional827 rhoQ omega chi selectedPlace yStar = 1

namespace NormalizedReflectedClass827

variable {rhoQ omega chi distinguishedPlace wild selectedPlace}
  {extension : ReflectedWildCarrierExtension827
    (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
    rhoQ omega chi distinguishedPlace wild}

omit [Fintype Delta]
  [Invertible (Fintype.card Delta : PadicInt 59)] in
/-- The normalization field is exactly selected 827 localization.  It is not
a statement about the pairing of `yStar` with the Fermat class. -/
theorem yStar_localization_eq_one
    (normalized : NormalizedReflectedClass827 rhoQ omega chi
      distinguishedPlace wild selectedPlace extension) :
    reflectedPointedLocalization827 rhoQ omega chi selectedPlace
        normalized.yStar = 1 := by
  simpa using normalized.normalization

/-- Fixing the missing normalized reflected class gives the correctly
variant wild functional on `H_FLT`. -/
def yStarPairingFunctional
    (normalized : NormalizedReflectedClass827 rhoQ omega chi
      distinguishedPlace wild selectedPlace extension) :
    H_FLT SelmerChi →+ ZMod 59 where
  toFun := fun x => extension.qRelaxedWild.reading x normalized.yStar
  map_zero' := by simp
  map_add' := by
    intro x y
    simp

end NormalizedReflectedClass827

end Fermat.FiftyNine.Conservation.UlamTypeFreeze
