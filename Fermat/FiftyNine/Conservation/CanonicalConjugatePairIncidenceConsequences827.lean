/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Concrete Poitou--Tate gain allocation for the canonical 827 lift

The canonical conjugate-pair lift supplies the pointed incidence package,
and canonical cyclotomic Fourier seating is already proved.  The generic
Poitou--Tate conservation law therefore allocates the one-dimensional local
gain completely to the reflected obstruction: reflected gain is one and
primal steering gain is zero.  Equivalently, the pointed conormal class is
zero and the class/nonpointed-silence kernel has fixed pointed attention.

These are consequences inside the 827 localization diagram.  They do not
identify that conormal class with the independently allocated Fermat
relation-(7a) class gauge.
-/
import Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidenceConsequences827

open Fermat.Conservation
open Fermat.Conservation.SteeringFiber
open Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.GaugeSteering827
open Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59
open Fermat.FiftyNine.Conservation.PointedTateIncidence
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- Canonical Fourier seating allocates the complete local dimension to the
reflected obstruction side of the actual pointed incidence sequence. -/
theorem canonicalConjugatePairReflectedGain827_eq_one :
    ((canonicalConjugatePairPointedIncidence827 (K := K)).toPoitouTateFiveTerm).reflectedDualObstructionGain = 1 :=
  reflectedGain_eq_one_of_fourierSeating
    (cyclotomicQRelaxedSelmerRepresentation827 K)
    canonicalTeichmullerCharacter59 irregularCharacter59
    (tameOrbitBasePlace827 (K := K))
    (canonicalConjugatePairPointedIncidence827 (K := K))
    (normalizedQLocalizationEquivariance827 K
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))

/-- By the conserved-bit identity, the complementary primal steering gain
is exactly zero. -/
theorem canonicalConjugatePairPrimalGain827_eq_zero :
    ((canonicalConjugatePairPointedIncidence827 (K := K)).toPoitouTateFiveTerm).primalSteeringGain = 0 := by
  have hbalance :=
    (canonicalConjugatePairPointedIncidence827 (K := K)).conserved_bit
  rw [canonicalConjugatePairReflectedGain827_eq_one] at hbalance
  omega

/-- The actual pointed conormal class of the canonical incidence is zero. -/
theorem canonicalConjugatePairPointedConormalClass827_eq_zero :
    pointedConormalClass827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (tameOrbitBasePlace827 (K := K)) = 0 :=
  (PointedTateIncidence827.conormalClass_eq_zero_iff_primalGain_eq_zero
    (canonicalConjugatePairPointedIncidence827 (K := K))).mpr
      canonicalConjugatePairPrimalGain827_eq_zero

/-- Equivalently, once projected class and every nonpointed 827 coordinate
vanish, the selected pointed coordinate must vanish as well. -/
theorem canonicalConjugatePairFixedAttention827 :
    FixedAttention
      (relaxedClassProjection827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59)
      (tameSilence827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (tameOrbitBasePlace827 (K := K)))
      (pointedCoordinate827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (tameOrbitBasePlace827 (K := K))) :=
  (PointedTateIncidence827.reflectedGain_eq_one_iff_fixed
    (canonicalConjugatePairPointedIncidence827 (K := K))).mp
      canonicalConjugatePairReflectedGain827_eq_one

end Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidenceConsequences827
