/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Pointed incidence from the canonical conjugate-pair lift

The canonical conjugate-pair construction now supplies the formerly open
reflected localization lift at 827.  Canonical cyclotomic Fourier seating
therefore turns that concrete lift into the actual pointed Poitou--Tate
incidence package.  The same package proves nonvanishing of the reflected
boundary functional and inhabits the retained normalized fiber.

This is geometric downstream composition only.  It supplies no reciprocity
law, class-gauge comparison, relation (7a), or Fermat endpoint.
-/
import Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827
import Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827

open Fermat.Conservation
open Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59
open Fermat.FiftyNine.Conservation.PointedTateIncidence
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- The canonical lift is based at the same explicit 827 place used by the
global tame orbit. -/
@[simp]
theorem canonicalBaseConjugatePairLift827_selectedPlace :
    (canonicalBaseConjugatePairLift827 (K := K)).selectedPlace =
      tameOrbitBasePlace827 (K := K) :=
  rfl

/-- Its source is literally the plus-provenance conjugate-pair source, not a
separately chosen localization witness. -/
@[simp]
theorem canonicalBaseConjugatePairLift827_source :
    (canonicalBaseConjugatePairLift827 (K := K)).source =
      Fermat.FiftyNine.Conservation.ConjugatePairSource827.conjugatePairSource827
        (tameOrbitBasePlace827 (K := K)) :=
  rfl

/-- The concrete reflected lift and canonical Fourier seating construct the
pointed Poitou--Tate incidence package at the actual base place. -/
noncomputable def canonicalConjugatePairPointedIncidence827 :
    PointedTateIncidence827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)) := by
  simpa using
    normalizedPointedIncidence59OfLiftCanonical K
      canonicalTeichmullerCharacter59 irregularCharacter59
      (canonicalBaseConjugatePairLift827 (K := K))

/-- The reflected boundary functional is unconditionally nonzero in the
canonical `(59, 44)` channel. -/
theorem canonicalConjugatePairBoundaryFunctional827_ne_zero :
    reflectedBoundaryFunctional827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (tameOrbitBasePlace827 (K := K)) ≠ 0 :=
  normalizedBoundaryFunctional59_ne_zero K
    canonicalTeichmullerCharacter59 irregularCharacter59
    (tameOrbitBasePlace827 (K := K))
    (canonicalConjugatePairPointedIncidence827 (K := K))
    (normalizedQLocalizationEquivariance827 K
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))

/-- The normalized reflected fiber retained by the Ulam readout is
unconditionally inhabited in the canonical channel. -/
theorem canonicalConjugatePairNormalizedReflectedFiber827_nonempty :
    Nonempty (NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :=
  normalizedReflectedFiber59_nonempty K
    canonicalTeichmullerCharacter59 irregularCharacter59
    (tameOrbitBasePlace827 (K := K))
    (canonicalConjugatePairPointedIncidence827 (K := K))
    (normalizedQLocalizationEquivariance827 K
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))

end Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827
