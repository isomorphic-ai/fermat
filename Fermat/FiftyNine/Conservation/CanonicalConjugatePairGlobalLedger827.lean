/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The concrete canonical conjugate-pair global ledger at 827

The canonical conjugate-pair construction now supplies the reflected lift
that the globally oriented 827 ledger previously accepted as a parameter.
This file installs that lift in the existing ledger, proves that the
resulting concrete ledger is live but has cancelling total, and specializes
the global-reciprocity endpoint at the actual wild place above 59.

Global reciprocity, comparison with all 58 local orbit readings, and silence
away from the wild and 827 places remain explicit hypotheses.  This module
does not manufacture any of those genuinely local-global inputs.
-/
import Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827
import Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827

open scoped NumberField

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.TatePairing
open Fermat.FiftyNine.Conservation.ActualTameLedger827
open Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827
open Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827
open Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CanonicalTameLedger827
open Fermat.FiftyNine.Conservation.CyclotomicTameContext59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.LocalReduction827
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- The canonical local value at orbit coordinate `tau`, with the actual
base-place conjugate-pair lift installed. -/
noncomputable def canonicalConjugatePairTameOrbitValue827
    (tau : GaloisIndex59) : ZMod 59 :=
  canonicalTameOrbitValue827 (K := K) canonicalTeichmullerCharacter59
    irregularCharacter59 (canonicalBaseConjugatePairLift827 (K := K)) tau

/-- The globally root-oriented 827 tame ledger of the canonical
conjugate-pair lift.  There is no remaining lift parameter. -/
noncomputable def canonicalConjugatePairGlobalLedger827 :
    Place K →₀ ZMod 59 :=
  canonicalTameLedger827 (K := K) canonicalTeichmullerCharacter59
    irregularCharacter59 (canonicalBaseConjugatePairLift827 (K := K))

@[simp]
theorem canonicalConjugatePairGlobalLedger827_apply_orbit
    (tau : GaloisIndex59) :
    canonicalConjugatePairGlobalLedger827 (K := K)
        (tameOrbitPlace827 (K := K) tau) =
      canonicalConjugatePairTameOrbitValue827 (K := K) tau := by
  exact canonicalTameLedger827_apply_orbit
    (K := K) canonicalTeichmullerCharacter59 irregularCharacter59
      (canonicalBaseConjugatePairLift827 (K := K)) tau

/-- The concrete globally normalized ledger has cancelling scalar total. -/
theorem canonicalConjugatePairGlobalLedger827_sum_eq_zero :
    (canonicalConjugatePairGlobalLedger827 (K := K)).sum
        (fun _ value ↦ value) = 0 := by
  exact canonicalTameLedger827_canonical_irregular_sum_eq_zero
    (canonicalBaseConjugatePairLift827 (K := K))

/-- The zero total above is genuine cancellation: the concrete ledger has a
nonzero local entry. -/
theorem canonicalConjugatePairGlobalLedger827_ne_zero :
    canonicalConjugatePairGlobalLedger827 (K := K) ≠ 0 := by
  exact canonicalTameLedger827_canonical_irregular_ne_zero
    (canonicalBaseConjugatePairLift827 (K := K))

universe uChi uDual

variable {SelmerChi : Type uChi} {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra 59 GaloisIndex59) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra 59 GaloisIndex59)
    DOmegaSelmerChiStar]
  {pairing : PlaceIndexedLocalPairing 59 GaloisIndex59
    canonicalTeichmullerCharacter59 irregularCharacter59
    (Place K) SelmerChi DOmegaSelmerChiStar}

/-- Genuine global reciprocity at the canonical conjugate-pair ledger forces
the actual wild pairing to vanish.  The canonical lift is installed by this
theorem; callers still provide the honest local comparison on the complete
827 orbit and silence at every other nonwild place. -/
theorem pairAt_lambdaPlace59_eq_zero_of_canonicalConjugatePair827
    (reciprocity : GlobalReciprocityLaw pairing)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (horbit : ∀ tau : GaloisIndex59,
      pairing.pairAt (tameOrbitPlace827 (K := K) tau) x y =
        canonicalConjugatePairTameOrbitValue827 (K := K) tau)
    (houtside : ∀ v : Place K, v ≠ lambdaPlace59 K →
      v ∉ placesOver827 K → pairing.pairAt v x y = 0) :
    pairing.pairAt (lambdaPlace59 K) x y = 0 := by
  exact pairAt_lambdaPlace59_eq_zero_of_globalReciprocity827
    (pairing := pairing) reciprocity
      (canonicalBaseConjugatePairLift827 (K := K)) x y horbit houtside

end Fermat.FiftyNine.Conservation.CanonicalConjugatePairGlobalLedger827
