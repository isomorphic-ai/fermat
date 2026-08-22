/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The genuine Fermat-factor input in the canonical full-orbit pairing

This file composes the solution-dependent odd primal source with the
canonical reflected 827 lift.  The resulting finite ledger is therefore
evaluated on two literal Mathlib Selmer classes:

* the normalized plus factor of the hypothetical Fermat solution, inserted
  through its 59th-power ideal root and projected to `chi = omega^15`;
* the constructed conjugate-pair reflected candidate in mode 44.

The distinguished row and every tame orbit row are exposed exactly.  A
global reciprocity law, when available, annihilates the complete ledger.
No reciprocity producer or nonvanishing value is asserted here.
-/
import Fermat.Exponents.FiftyNine.Conservation.CanonicalConjugatePairLift827
import Fermat.Exponents.FiftyNine.Conservation.FermatFactorSelmerSource59
import Fermat.Exponents.FiftyNine.Conservation.FullOrbitGlobalReciprocityCriterion827

open scoped BigOperators MonoidAlgebra NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.CanonicalFermatFactorFullOrbitEndpoint827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TatePairing
open ActualTameLedger827
open CanonicalConjugatePairLift827
open CanonicalFullOrbitLocalPairing827
open CanonicalIrregularMode827
open CanonicalTameLedger827
open CyclotomicSelmerAction59
open CyclotomicTameContext59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open FermatFactorSelmerSource59
open FullOrbitGlobalReciprocityCriterion827
open LocalCompletion59
open NormalizedContinuousKummerPairing59
open SplitPrimeFourier827
open StateFactorPair

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  {ζ : K} {hζ : IsPrimitiveRoot ζ 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

local instance residueIdealIsMaximal
    (v : Place K) : v.asIdeal.IsMaximal := v.isMaximal

local instance residueField (v : Place K) : Field (Residue K v) :=
  Ideal.Quotient.field v.asIdeal

local instance residueFintype (v : Place K) : Fintype (Residue K v) :=
  Fintype.ofFinite _

/-- The canonical reflected candidate used in the complete orbit pairing. -/
noncomputable abbrev canonicalReflectedCandidate827 :
    QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59 :=
  (canonicalBaseConjugatePairLift827 (K := K)).candidate

/-- The complete normalized-wild/58-tame ledger evaluated on the genuine
Fermat plus-factor source and the canonical reflected candidate. -/
noncomputable def fermatFactorFullOrbitLedger827
    (pair : StateLinkedIdealPair hζ S hz) : Place K →₀ ZMod 59 :=
  (canonicalFullOrbitLocalPairing827 K
      canonicalTeichmullerCharacter59 irregularCharacter59).readings
    (fermatPlusPrimalMode59 pair)
    (canonicalReflectedCandidate827 (K := K))

/-- The wild row is exactly the normalized local Kummer pairing on the two
literal global classes. -/
@[simp]
theorem fermatFactorFullOrbitLedger827_lambda
    (pair : StateLinkedIdealPair hζ S hz) :
    fermatFactorFullOrbitLedger827 pair (lambdaPlace59 K) =
      normalizedLambdaGlobalPairing59 K
        (toKummerClass (fermatPlusPrimalMode59 pair))
        (toKummerClassAt (canonicalReflectedCandidate827 (K := K))) := by
  change
    (canonicalFullOrbitLocalPairing827 K
      canonicalTeichmullerCharacter59 irregularCharacter59).pairAt
        (lambdaPlace59 K) (fermatPlusPrimalMode59 pair)
        (canonicalReflectedCandidate827 (K := K)) = _
  exact canonicalFullOrbitLocalPairing827_pairAt_lambda K
    canonicalTeichmullerCharacter59 irregularCharacter59
    (fermatPlusPrimalMode59 pair)
    (canonicalReflectedCandidate827 (K := K))

/-- Every retained tame row is the actual globally-root-oriented tame
symbol on the same two global Kummer classes. -/
@[simp]
theorem fermatFactorFullOrbitLedger827_orbit
    (pair : StateLinkedIdealPair hζ S hz) (tau : GaloisIndex59) :
    fermatFactorFullOrbitLedger827 pair
        (tameOrbitPlace827 (K := K) tau) =
      (context K (tameOrbitPlace827 (K := K) tau)
        (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).modP
          (toKummerClass (fermatPlusPrimalMode59 pair))
          (toKummerClassAt
            (canonicalReflectedCandidate827 (K := K))) := by
  change
    (canonicalFullOrbitLocalPairing827 K
      canonicalTeichmullerCharacter59 irregularCharacter59).pairAt
        (tameOrbitPlace827 (K := K) tau)
        (fermatPlusPrimalMode59 pair)
        (canonicalReflectedCandidate827 (K := K)) = _
  exact canonicalFullOrbitLocalPairing827_pairAt_orbit K
    canonicalTeichmullerCharacter59 irregularCharacter59 tau
    (fermatPlusPrimalMode59 pair)
    (canonicalReflectedCandidate827 (K := K))

/-- Exact expansion of the total literal ledger. -/
theorem fermatFactorFullOrbitLedger827_sum_eq
    (pair : StateLinkedIdealPair hζ S hz) :
    (fermatFactorFullOrbitLedger827 pair).sum (fun _ value ↦ value) =
      normalizedLambdaGlobalPairing59 K
          (toKummerClass (fermatPlusPrimalMode59 pair))
          (toKummerClassAt
            (canonicalReflectedCandidate827 (K := K))) +
        ∑ tau : GaloisIndex59,
          (context K (tameOrbitPlace827 (K := K) tau)
            (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).modP
              (toKummerClass (fermatPlusPrimalMode59 pair))
              (toKummerClassAt
                (canonicalReflectedCandidate827 (K := K))) := by
  change
    ((canonicalFullOrbitLocalPairing827 K
      canonicalTeichmullerCharacter59 irregularCharacter59).readings
        (fermatPlusPrimalMode59 pair)
        (canonicalReflectedCandidate827 (K := K))).sum
          (fun _ value ↦ value) = _
  exact canonicalFullOrbitLocalPairing827_readings_sum_eq K
    canonicalTeichmullerCharacter59 irregularCharacter59
    (fermatPlusPrimalMode59 pair)
    (canonicalReflectedCandidate827 (K := K))

/-- Global reciprocity, stated on the already constructed full pairing,
annihilates the genuine Fermat-factor/conjugate-pair ledger. -/
theorem fermatFactorFullOrbitLedger827_sum_eq_zero_of_reciprocity
    (pair : StateLinkedIdealPair hζ S hz)
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59)) :
    (fermatFactorFullOrbitLedger827 pair).sum (fun _ value ↦ value) = 0 :=
  reciprocity.sum_eq_zero
    (fermatPlusPrimalMode59 pair)
    (canonicalReflectedCandidate827 (K := K))

/-- The same ledger with the ideal allocation selected canonically from the
Fermat state. -/
noncomputable def canonicalFermatFactorFullOrbitLedger827
    (hζ : IsPrimitiveRoot ζ 59)
    (S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution)
    (hz : (59 : ℤ) ∣ S.z) : Place K →₀ ZMod 59 :=
  fermatFactorFullOrbitLedger827 (allocatedPair hζ S hz)

/-- The canonical statewise ledger is likewise zero under the single honest
global-reciprocity seam. -/
theorem canonicalFermatFactorFullOrbitLedger827_sum_eq_zero_of_reciprocity
    (hζ : IsPrimitiveRoot ζ 59)
    (S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution)
    (hz : (59 : ℤ) ∣ S.z)
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59)) :
    (canonicalFermatFactorFullOrbitLedger827 hζ S hz).sum
        (fun _ value ↦ value) = 0 :=
  fermatFactorFullOrbitLedger827_sum_eq_zero_of_reciprocity
    (allocatedPair hζ S hz) reciprocity

end Fermat.FiftyNine.Conservation.CanonicalFermatFactorFullOrbitEndpoint827
