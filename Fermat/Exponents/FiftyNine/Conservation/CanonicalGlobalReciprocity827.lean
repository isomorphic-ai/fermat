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
import Fermat.Exponents.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827
import Fermat.Exponents.FiftyNine.Conservation.LocalCompletion59
import Fermat.Experiments.Conservation.FiniteOrbitLedgerReciprocity
import Fermat.Experiments.Conservation.TatePairing

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
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

universe uChi uDual

variable {K : Type} [Field K] [NumberField K]
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

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The actual wild cyclotomic place above 59 is not one of the auxiliary
places above 827. -/
theorem lambdaPlace59_not_mem_placesOver827 :
    lambdaPlace59 K ∉ placesOver827 K := by
  intro h827
  have h59 : Ideal.span ({(59 : ℤ)} : Set ℤ) =
      (lambdaPlace59 K).asIdeal.under ℤ :=
    (lambdaIdeal59_liesOver K).over
  have heq : Ideal.span ({(59 : ℤ)} : Set ℤ) =
      Ideal.span ({(Credit.attestationPrime : ℤ)} : Set ℤ) :=
    h59.trans h827.symm
  have hmem : (59 : ℤ) ∈
      Ideal.span ({(Credit.attestationPrime : ℤ)} : Set ℤ) := by
    rw [← heq]
    exact Ideal.subset_span (by simp)
  rw [Ideal.mem_span_singleton] at hmem
  norm_num [Credit.attestationPrime] at hmem

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
private theorem tameOrbitPlace827_ne_distinguished
    (distinguished : Place K)
    (hdistinguished : distinguished ∉ placesOver827 K) :
    ∀ tau : GaloisIndex59,
      tameOrbitPlace827 (K := K) tau ≠ distinguished := by
  intro tau hplace
  apply hdistinguished
  rw [← tameOrbitPlace827_range_eq_placesOver827 (K := K)]
  exact ⟨tau, hplace⟩

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
  have houtsideRange : ∀ v : Place K, v ≠ distinguished →
      v ∉ Set.range (tameOrbitPlace827 (K := K)) →
      pairing.pairAt v x y = 0 := by
    simpa only [tameOrbitPlace827_range_eq_placesOver827 (K := K)] using
      houtside
  simpa only [canonicalTameLedger827] using
    (FiniteOrbitLedgerReciprocity.readings_eq_single_add_orbitLedger
      (pairing := pairing) distinguished (tameOrbitPlace827 (K := K))
      (tameOrbitPlace827_injective (K := K))
      (tameOrbitPlace827_ne_distinguished
        (K := K) distinguished hdistinguished)
      x y wildReading hwild
      (canonicalTameOrbitValue827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 lift)
      horbit houtsideRange)

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
  have houtsideRange : ∀ v : Place K, v ≠ distinguished →
      v ∉ Set.range (tameOrbitPlace827 (K := K)) →
      pairing.pairAt v x y = 0 := by
    simpa only [tameOrbitPlace827_range_eq_placesOver827 (K := K)] using
      houtside
  simpa only [canonicalTameLedger827] using
    (FiniteOrbitLedgerReciprocity.wild_add_orbitLedger_sum_eq_zero_of_globalReciprocity
      (pairing := pairing) reciprocity distinguished
      (tameOrbitPlace827 (K := K))
      (tameOrbitPlace827_injective (K := K))
      (tameOrbitPlace827_ne_distinguished
        (K := K) distinguished hdistinguished)
      x y wildReading hwild
      (canonicalTameOrbitValue827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 lift)
      horbit houtsideRange)

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
  have houtsideRange : ∀ v : Place K, v ≠ distinguished →
      v ∉ Set.range (tameOrbitPlace827 (K := K)) →
      pairing.pairAt v x y = 0 := by
    simpa only [tameOrbitPlace827_range_eq_placesOver827 (K := K)] using
      houtside
  apply
    FiniteOrbitLedgerReciprocity.pairAt_eq_zero_of_globalReciprocity_of_orbitLedger_sum_eq_zero
      (pairing := pairing) reciprocity distinguished
      (tameOrbitPlace827 (K := K))
      (tameOrbitPlace827_injective (K := K))
      (tameOrbitPlace827_ne_distinguished
        (K := K) distinguished hdistinguished)
      x y
      (canonicalTameOrbitValue827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 lift)
      horbit houtsideRange
  simpa only [canonicalTameLedger827] using
    canonicalTameLedger827_canonical_irregular_sum_eq_zero lift

/-- The same endpoint at the repository's concrete wild place
`lambda = (zeta_59 - 1)`.  Its disjointness from the complete 827 orbit is
proved above and is no longer an input. -/
theorem pairAt_lambdaPlace59_eq_zero_of_globalReciprocity827
    (reciprocity : GlobalReciprocityLaw pairing)
    (lift : ReflectedQRelaxedLocalizationLift827
      (LocalReduction827.rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59)
    (x : SelmerChi) (y : DOmegaSelmerChiStar)
    (horbit : ∀ tau : GaloisIndex59,
      pairing.pairAt (tameOrbitPlace827 (K := K) tau) x y =
        canonicalTameOrbitValue827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 lift tau)
    (houtside : ∀ v : Place K, v ≠ lambdaPlace59 K →
      v ∉ placesOver827 K → pairing.pairAt v x y = 0) :
    pairing.pairAt (lambdaPlace59 K) x y = 0 :=
  pairAt_distinguished_eq_zero_of_globalReciprocity827
    (pairing := pairing) reciprocity lift (lambdaPlace59 K)
      (lambdaPlace59_not_mem_placesOver827 (K := K)) x y horbit houtside

end Fermat.FiftyNine.Conservation.CanonicalGlobalReciprocity827
