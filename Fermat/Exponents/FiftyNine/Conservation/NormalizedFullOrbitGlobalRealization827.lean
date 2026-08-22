/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The normalized reflected fiber realizes the complete 827 orbit profile

The canonical conjugate-pair construction makes the retained normalized
reflected fiber nonempty.  Cyclotomic localization equivariance then shows
that every point of this fiber has exactly the normalized inverse-reflected
coordinate vector on the complete orbit above `827`.

The public object remains the whole normalized fiber.  The final existence
theorem merely exposes an actual relaxed carrier realizing the profile; it
does not choose or name a distinguished point of the fiber.  No wild-place
compatibility, Poitou--Tate lifting theorem, Artin comparison, reciprocity
law, relation `(7a)`, or Fermat endpoint is asserted here.
-/
import Fermat.Exponents.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827
import Fermat.Exponents.FiftyNine.Conservation.CanonicalConjugatePairIncidence827
import Fermat.Exponents.FiftyNine.Conservation.NormalizedFullOrbitEigenprofile827

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.ActualTameLedger827
open Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827
open Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827
open Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.NormalizedFullOrbitEigenprofile827
open Fermat.FiftyNine.Conservation.PointedTateIncidence
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- Every receipt in the normalized reflected fiber has the full normalized
inverse-reflected coordinate profile on the genuine `827`-orbit.  The left
side is Mathlib's supported Selmer valuation on the underlying relaxed
carrier, not supplied coordinate data. -/
theorem normalizedReflectedFiber827_relaxedOrbitValuation_eq_profile
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K)))
    (tau : GaloisIndex59) :
    relaxedOrbitValuation827 K tau y.1.1 =
      normalizedFullOrbitEigenprofileCoordinates827 omega chi tau := by
  let rhoQ := cyclotomicQRelaxedSelmerRepresentation827 K
  have hprojector :
      qRelaxedReflectedProjector827 rhoQ omega chi y.1.1 = y.1 := by
    apply Subtype.ext
    exact characterProjectorAt_eq_self_of_mem rhoQ
      (InvolutiveBase.reflectedCharacter omega chi) y.1.1 y.1.2
  have hbase :
      qLocalizationCoordinate827 rhoQ omega chi
          (tameOrbitBasePlace827 (K := K)) y.1 = 1 := by
    rw [← reflectedBoundaryFunctional827_eq_qLocalizationCoordinate827]
    exact y.2
  have horbit :=
    (cyclotomicQLocalizationEquivariance827 K omega chi
      (tameOrbitBasePlace827 (K := K))).projected_coordinate_orbit tau y.1.1
  rw [hprojector, hbase, mul_one] at horbit
  have hplace :
      orbitSupportPlace827 K tau =
        indexedPlaceOrbitEquiv827 K
          (tameOrbitBasePlace827 (K := K)) tau := by
    apply Subtype.ext
    rfl
  change supportValuationAt (orbitSupportPlace827 K tau) y.1.1 = _
  rw [hplace]
  exact horbit

/-- Consequently, the genuine supported-valuation vector of every normalized
fiber receipt is the pure inverse-reflected Fourier mode. -/
theorem normalizedReflectedFiber827_relaxedOrbitValuation_isPureCharacter
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (tameOrbitBasePlace827 (K := K))) :
    IsPureCharacter (inverseReflectedResidueCharacter827 omega chi)
      (fun tau : GaloisIndex59 ↦ relaxedOrbitValuation827 K tau y.1.1) := by
  have hcoordinates :
      (fun tau : GaloisIndex59 ↦ relaxedOrbitValuation827 K tau y.1.1) =
        normalizedFullOrbitEigenprofileCoordinates827 omega chi := by
    funext tau
    exact normalizedReflectedFiber827_relaxedOrbitValuation_eq_profile
      omega chi y tau
  rw [hcoordinates]
  exact normalizedFullOrbitEigenprofileCoordinates827_isPureCharacter omega chi

/-- In the canonical irregular `(59, 44)` channel, an actual global
`827`-relaxed Selmer carrier realizes the complete normalized orbit profile.
This existential is deliberately weaker than choosing a distinguished point
of the retained normalized fiber. -/
theorem exists_relaxedCarrier827_realizing_normalizedFullOrbitEigenprofile :
    ∃ y : RelaxedCarrier827 K,
      y ∈ characterEigenspaceAt
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          (InvolutiveBase.reflectedCharacter
            canonicalTeichmullerCharacter59 irregularCharacter59) ∧
        ∀ tau : GaloisIndex59,
          relaxedOrbitValuation827 K tau y =
            normalizedFullOrbitEigenprofileCoordinates827
              canonicalTeichmullerCharacter59 irregularCharacter59 tau := by
  obtain ⟨y⟩ :=
    canonicalConjugatePairNormalizedReflectedFiber827_nonempty (K := K)
  refine ⟨y.1.1, y.1.2, ?_⟩
  intro tau
  exact normalizedReflectedFiber827_relaxedOrbitValuation_eq_profile
    canonicalTeichmullerCharacter59 irregularCharacter59 y tau

end Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827
