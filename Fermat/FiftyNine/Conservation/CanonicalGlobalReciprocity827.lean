/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Global reciprocity applied to the canonical 827 tame ledger

The globally oriented tame ledger is an explicit `Finsupp` on genuine
height-one places.  This file connects it to the repository's existing
`GlobalReciprocityLaw` interface.  The bridge consumes only the remaining
local comparison data: the distinguished wild reading, equality with the
canonical tame values on the complete 827 orbit, and silence away from those
places.

No reciprocity producer, local pairing value, or reflected lift is
manufactured here.  In the canonical `(59,44)` seat the already proved tame
cancellation then forces the distinguished reading to vanish.
-/
import Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827
import Fermat.Conservation.TatePairing

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.TatePairing
open Fermat.FiftyNine.Conservation.ActualTameLedger827
open Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CanonicalTameLedger827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.CyclotomicTameContext59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.LocalReduction827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

universe uChi uDual

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  {SelmerChi : Type uChi} {DOmegaSelmerChiStar : Type uDual}
  [AddCommGroup SelmerChi]
  [Module (IntegralPadicGroupAlgebra 59 GaloisIndex59) SelmerChi]
  [AddCommGroup DOmegaSelmerChiStar]
  [Module (IntegralPadicGroupAlgebra 59 GaloisIndex59)
    DOmegaSelmerChiStar]
  {pairing : PlaceIndexedLocalPairing 59 GaloisIndex59
    canonicalTeichmullerCharacter59 irregularCharacter59
    (Place K) SelmerChi DOmegaSelmerChiStar}

/-- Pointwise local comparison identifies the pairing's complete retained
ledger with one distinguished wild entry plus the canonical 827 tame
ledger.  Exhaustivity of the explicit 58-place orbit handles every place
over 827; the supplied silence law handles every remaining place. -/
theorem readings_eq_single_add_canonicalTameLedger827
    (lift : ReflectedQRelaxedLocalizationLift827
      (LocalReduction827.rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59)
    (distinguished : Place K) (hdistinguished : distinguished ∉ placesOver827 K)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) (wildReading : ZMod 59)
    (hwild : pairing.pairAt distinguished x y = wildReading)
    (horbit : ∀ tau : GaloisIndex59,
      pairing.pairAt (tameOrbitPlace827 (K := K) tau) x y =
        canonicalTameOrbitValue827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 lift tau)
    (houtside : ∀ v : Place K, v ≠ distinguished →
      v ∉ placesOver827 K → pairing.pairAt v x y = 0) :
    pairing.readings x y =
      Finsupp.single distinguished wildReading +
        canonicalTameLedger827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 lift := by
  classical
  ext v
  change pairing.pairAt v x y = _
  by_cases hvd : v = distinguished
  · subst v
    rw [hwild, Finsupp.add_apply, Finsupp.single_eq_same,
      canonicalTameLedger827_apply_eq_zero_of_not_over827
        (K := K) canonicalTeichmullerCharacter59 irregularCharacter59
        lift distinguished hdistinguished,
      add_zero]
  · by_cases hq : v ∈ placesOver827 K
    · let orbitEquiv := indexedPlaceOrbitEquiv827 K
        (tameOrbitBasePlace827 (K := K))
      let tau : GaloisIndex59 := orbitEquiv.symm ⟨v, hq⟩
      have htau : tameOrbitPlace827 (K := K) tau = v := by
        exact congrArg Subtype.val (orbitEquiv.apply_symm_apply ⟨v, hq⟩)
      rw [← htau, horbit tau, Finsupp.add_apply]
      have hne : distinguished ≠ tameOrbitPlace827 (K := K) tau := by
        intro h
        apply hvd
        rw [← htau]
        exact h.symm
      simp [hne]
    · rw [houtside v hvd hq, Finsupp.add_apply,
        canonicalTameLedger827_apply_eq_zero_of_not_over827
          (K := K) canonicalTeichmullerCharacter59 irregularCharacter59
          lift v hq]
      simp [Ne.symm hvd]

/-- The existing global-reciprocity interface turns the pointwise local
comparison into the exact scalar balance against the canonical tame ledger.
This removes the formerly hand-supplied balance equation without claiming a
producer for the reciprocity interface itself. -/
theorem wild_add_canonicalTameLedger827_sum_eq_zero_of_globalReciprocity
    (reciprocity : GlobalReciprocityLaw pairing)
    (lift : ReflectedQRelaxedLocalizationLift827
      (LocalReduction827.rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59)
    (distinguished : Place K) (hdistinguished : distinguished ∉ placesOver827 K)
    (x : SelmerChi) (y : DOmegaSelmerChiStar) (wildReading : ZMod 59)
    (hwild : pairing.pairAt distinguished x y = wildReading)
    (horbit : ∀ tau : GaloisIndex59,
      pairing.pairAt (tameOrbitPlace827 (K := K) tau) x y =
        canonicalTameOrbitValue827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 lift tau)
    (houtside : ∀ v : Place K, v ≠ distinguished →
      v ∉ placesOver827 K → pairing.pairAt v x y = 0) :
    wildReading +
        (canonicalTameLedger827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 lift).sum
            (fun _ value ↦ value) = 0 := by
  have hreadings := readings_eq_single_add_canonicalTameLedger827
    (pairing := pairing) lift distinguished hdistinguished x y wildReading
    hwild horbit houtside
  calc
    wildReading +
        (canonicalTameLedger827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 lift).sum
            (fun _ value ↦ value) =
      (Finsupp.single distinguished wildReading +
        canonicalTameLedger827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 lift).sum
            (fun _ value ↦ value) := by
              rw [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
                Finsupp.sum_single_index (by rfl)]
    _ = (pairing.readings x y).sum (fun _ value ↦ value) := by
      rw [hreadings]
    _ = 0 := reciprocity.sum_eq_zero x y

/-- In the canonical irregular mode, genuine global reciprocity and the
explicit local comparison force the distinguished wild pairing value to
vanish.  The tame side disappears by proved cancellation of a nonzero
globally oriented ledger. -/
theorem pairAt_distinguished_eq_zero_of_globalReciprocity827
    (reciprocity : GlobalReciprocityLaw pairing)
    (lift : ReflectedQRelaxedLocalizationLift827
      (LocalReduction827.rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59)
    (distinguished : Place K) (hdistinguished : distinguished ∉ placesOver827 K)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (horbit : ∀ tau : GaloisIndex59,
      pairing.pairAt (tameOrbitPlace827 (K := K) tau) x y =
        canonicalTameOrbitValue827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 lift tau)
    (houtside : ∀ v : Place K, v ≠ distinguished →
      v ∉ placesOver827 K → pairing.pairAt v x y = 0) :
    pairing.pairAt distinguished x y = 0 := by
  have hbalance :=
    wild_add_canonicalTameLedger827_sum_eq_zero_of_globalReciprocity
      (pairing := pairing) reciprocity lift distinguished hdistinguished
      x y (pairing.pairAt distinguished x y) rfl horbit houtside
  rw [canonicalTameLedger827_canonical_irregular_sum_eq_zero,
    add_zero] at hbalance
  exact hbalance

end Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827
