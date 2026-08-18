/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The exact global-reciprocity criterion for the complete 827 orbit

`CanonicalFullOrbitLocalPairing827` constructs one normalized wild row and
all 58 genuine globally-root-oriented tame-symbol rows.  This file computes
the total of that finite ledger for arbitrary strict/reflected Selmer inputs.

The final theorem is an exact equivalence.  Global reciprocity for the
constructed pairing is precisely the assertion that the normalized lambda
reading plus the finite sum of the 58 explicit tame readings vanishes for
every pair of inputs.  No reciprocity producer or local value is introduced.
-/
import Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827

open scoped BigOperators MonoidAlgebra NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.FullOrbitGlobalReciprocityCriterion827

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TatePairing
open ActualTameLedger827
open CanonicalFullOrbitLocalPairing827
open CanonicalTameLedger827
open CyclotomicSelmerAction59
open CyclotomicTameContext59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open LocalCompletion59
open NormalizedContinuousKummerPairing59
open SplitPrimeFourier827
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance residueIdealIsMaximal
    (v : Place K) : v.asIdeal.IsMaximal := v.isMaximal

local instance residueField (v : Place K) : Field (Residue K v) :=
  Ideal.Quotient.field v.asIdeal

local instance residueFintype (v : Place K) : Fintype (Residue K v) :=
  Fintype.ofFinite _

/-- Summing the raw finite-support ledger is exactly its normalized wild
reading plus the finite sum of all 58 genuine tame readings. -/
theorem rawFullOrbitReadings827_sum_eq
    (x : StrictCarrier59 K) (y : RelaxedCarrier827 K) :
    (rawFullOrbitReadings827 K x y).sum (fun _ value ↦ value) =
      rawWildReading59 K x y +
        ∑ tau : GaloisIndex59, rawTameOrbitReading827 K tau x y := by
  classical
  let value : GaloisIndex59 → ZMod 59 :=
    fun tau ↦ rawTameOrbitReading827 K tau x y
  let place : GaloisIndex59 → Place K :=
    fun tau ↦ tameOrbitPlace827 (K := K) tau
  have hsum (s : Finset GaloisIndex59) :
      (∑ tau ∈ s, Finsupp.single (place tau) (value tau)).sum
          (fun _ entry ↦ entry) =
        ∑ tau ∈ s, value tau := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert tau s htau ih =>
        rw [Finset.sum_insert htau, Finset.sum_insert htau,
          Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
          Finsupp.sum_single_index (by rfl), ih]
  rw [rawFullOrbitReadings827_apply,
    Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
    Finsupp.sum_single_index (by rfl)]
  exact congrArg (rawWildReading59 K x y + ·)
    (hsum (Finset.univ : Finset GaloisIndex59))

section Seated

variable
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

/-- The total of the seated pairing expands to the normalized lambda Kummer
pairing plus the complete finite sum of canonical tame `modP` pairings. -/
theorem canonicalFullOrbitLocalPairing827_readings_sum_eq
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    ((canonicalFullOrbitLocalPairing827 K omega chi).readings x y).sum
        (fun _ value ↦ value) =
      normalizedLambdaGlobalPairing59 K
          (toKummerClass x) (toKummerClassAt y) +
        ∑ tau : GaloisIndex59,
          (context K (tameOrbitPlace827 (K := K) tau)
            (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).modP
              (toKummerClass x) (toKummerClassAt y) := by
  change (rawFullOrbitReadings827 K
      ((toSeatedCarrier
        (rho := cyclotomicStrictSelmerRepresentation59 K)
        (chi := chi)).toAddMonoidHom x)
      ((toSupportedCarrier
        (rho := cyclotomicQRelaxedSelmerRepresentation827 K)
        (eta := InvolutiveBase.reflectedCharacter omega chi)).toAddMonoidHom y)
      ).sum (fun _ value ↦ value) = _
  rw [rawFullOrbitReadings827_sum_eq]
  rfl

/-- **Exact remaining reciprocity theorem.**  The constructed full-orbit
pairing satisfies global reciprocity if and only if its literal normalized
wild row plus all 58 literal tame rows balances to zero for every pair of
global seated Selmer classes. -/
theorem globalReciprocityLaw_canonicalFullOrbitLocalPairing827_iff :
    GlobalReciprocityLaw (canonicalFullOrbitLocalPairing827 K omega chi) ↔
      ∀ (x : OldPrimal59
          (cyclotomicStrictSelmerRepresentation59 K) chi)
        (y : QRelaxedReflectedDual827
          (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi),
        normalizedLambdaGlobalPairing59 K
            (toKummerClass x) (toKummerClassAt y) +
          ∑ tau : GaloisIndex59,
            (context K (tameOrbitPlace827 (K := K) tau)
              (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).modP
                (toKummerClass x) (toKummerClassAt y) = 0 := by
  constructor
  · intro reciprocity x y
    rw [← canonicalFullOrbitLocalPairing827_readings_sum_eq]
    exact reciprocity.sum_eq_zero x y
  · intro balance
    exact ⟨fun x y ↦ by
      rw [canonicalFullOrbitLocalPairing827_readings_sum_eq]
      exact balance x y⟩

end Seated

end Fermat.FiftyNine.Conservation.FullOrbitGlobalReciprocityCriterion827
