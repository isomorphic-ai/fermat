/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The literal generated-unit/conjugate-pair readout

The first generated circular unit is a genuine strict Selmer class, and the
canonical conjugate-pair construction supplies a genuine reflected
q-relaxed class.  They cannot both be inserted into the old `chi = 15`
seated pairing: the generated unit is real, so its odd character projection
is zero.  The underlying Kummer pairing has no such artificial restriction.

This file therefore evaluates the raw, unseated wild-plus-complete-tame
ledger on those two literal classes.  At every place over 827 its value is
proved equal to the existing globally-root-oriented canonical tame symbol.
Thus the explicit canonical ledger is recovered from the actual quotient
pairing, rather than merely copied into a second finite-support object.

No global reciprocity theorem or nonzero wild value is asserted here.
-/
import Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
import Fermat.FiftyNine.Conservation.CanonicalPrimalSelmerMode827
import Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827

open scoped BigOperators MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.CanonicalRawConjugatePairReadout827

open Fermat.Conservation
open Fermat.Conservation.TameSymbol
open Fermat.FiftyNine.Conservation.ActualTameLedger827
open Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827
open Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
open Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CanonicalPrimalSelmerMode827
open Fermat.FiftyNine.Conservation.CanonicalTameLedger827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.CyclotomicTameContext59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.LocalReduction827
open Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

local instance residueIdealIsMaximal (v : Place K) :
    v.asIdeal.IsMaximal := v.isMaximal

local instance residueField (v : Place K) : Field (Residue K v) :=
  Ideal.Quotient.field v.asIdeal

local instance residueFintype (v : Place K) : Fintype (Residue K v) :=
  Fintype.ofFinite _

/-- The literal first generated circular unit after Mathlib's empty-support
Selmer inclusion, before applying any character projector. -/
noncomputable abbrev canonicalRawPrimal827 : StrictCarrier59 K :=
  canonicalFirstGeneratedStrictSelmer59 K

/-- The projected class retained by the canonical conjugate-pair lift,
viewed in its underlying 827-relaxed Selmer carrier. -/
noncomputable abbrev canonicalRawReflected827 : RelaxedCarrier827 K :=
  (canonicalBaseConjugatePairLift827 (K := K)).candidate.1

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The left raw Kummer input is represented by the literal global circular
unit used in the canonical tame ledger. -/
theorem canonicalRawPrimal827_kummerClass :
    strictKummerClass59 K (canonicalRawPrimal827 K) =
      Additive.ofMul (QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range
        (ReflectedQRelaxedLocalizationLift827.primalRepresentative
          (CanonicalPrimalSelmerMode827.canonicalZeta59_isPrimitive K))) := by
  exact canonicalFirstGeneratedStrictSelmer59_kummerClass K

/-- The right raw Kummer input is represented by the literal two-prime
supported representative retained by the canonical lift. -/
theorem canonicalRawReflected827_kummerClass :
    relaxedKummerClass827 K (canonicalRawReflected827 K) =
      Additive.ofMul (QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range
        (canonicalBaseConjugatePairLift827
          (K := K)).candidateRepresentative) := by
  change Additive.ofMul
      (SelmerEigenspace.toKummerQuotientAt
        (canonicalBaseConjugatePairLift827 (K := K)).candidate) = _
  exact congrArg Additive.ofMul
    (canonicalBaseConjugatePairLift827
      (K := K)).candidate_represents.symm

/-- Every raw tame row on the literal pair is the globally-root-oriented
canonical local symbol already used by the explicit 827 ledger. -/
theorem canonicalRawTameOrbitReading827_eq
    (tau : GaloisIndex59) :
    rawTameOrbitReading827 K tau
        (canonicalRawPrimal827 K) (canonicalRawReflected827 K) =
      canonicalTameOrbitValue827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (canonicalBaseConjugatePairLift827 (K := K)) tau := by
  rw [canonicalTameOrbitValue827_eq_context_at_place]
  change (context K (tameOrbitPlace827 (K := K) tau)
      (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).modP
        (strictKummerClass59 K (canonicalRawPrimal827 K))
        (relaxedKummerClass827 K (canonicalRawReflected827 K)) = _
  rw [canonicalRawPrimal827_kummerClass,
    canonicalRawReflected827_kummerClass]
  exact (context K (tameOrbitPlace827 (K := K) tau)
    (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).modP_mk_mk _ _

/-- Consequently every 827-place entry of the complete raw ledger recovers
the corresponding entry of the explicit canonical tame ledger. -/
@[simp]
theorem canonicalRawFullOrbitReadings827_apply_orbit
    (tau : GaloisIndex59) :
    rawFullOrbitReadings827 K
        (canonicalRawPrimal827 K) (canonicalRawReflected827 K)
        (tameOrbitPlace827 (K := K) tau) =
      canonicalTameLedger827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (canonicalBaseConjugatePairLift827 (K := K))
        (tameOrbitPlace827 (K := K) tau) := by
  rw [rawFullOrbitReadings827_apply_orbit,
    canonicalTameLedger827_apply_orbit,
    canonicalRawTameOrbitReading827_eq]

/-- Finsupp-level identification: the complete raw ledger on the literal
pair is exactly its one normalized wild row plus the already checked
globally-root-oriented tame ledger. -/
theorem canonicalRawFullOrbitReadings827_eq_single_add_canonicalLedger :
    rawFullOrbitReadings827 K
        (canonicalRawPrimal827 K) (canonicalRawReflected827 K) =
      Finsupp.single (lambdaPlace59 K)
          (rawWildReading59 K
            (canonicalRawPrimal827 K) (canonicalRawReflected827 K)) +
        canonicalTameLedger827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (canonicalBaseConjugatePairLift827 (K := K)) := by
  rw [rawFullOrbitReadings827_apply, canonicalTameLedger827]
  apply congrArg
    (fun ledger : Place K →₀ ZMod 59 ↦
      Finsupp.single (lambdaPlace59 K)
          (rawWildReading59 K
            (canonicalRawPrimal827 K) (canonicalRawReflected827 K)) +
        ledger)
  apply Finset.sum_congr rfl
  intro tau _
  exact congrArg
    (fun value : ZMod 59 ↦
      Finsupp.single (tameOrbitPlace827 (K := K) tau) value)
    (canonicalRawTameOrbitReading827_eq K tau)

/-- The globally oriented tame entries cancel, so summing this literal raw
ledger retains exactly the normalized wild row.  This is a computation of
the constructed ledger, not an assertion that its total vanishes. -/
theorem canonicalRawFullOrbitReadings827_sum_eq_rawWildReading :
    (rawFullOrbitReadings827 K
        (canonicalRawPrimal827 K) (canonicalRawReflected827 K)).sum
          (fun _ value ↦ value) =
      rawWildReading59 K
        (canonicalRawPrimal827 K) (canonicalRawReflected827 K) := by
  rw [canonicalRawFullOrbitReadings827_eq_single_add_canonicalLedger,
    Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl),
    Finsupp.sum_single_index (by rfl),
    canonicalTameLedger827_canonical_irregular_sum_eq_zero,
    add_zero]

/-- Quotient-level form of the same conservation receipt: after the tame
cancellation, the total is the genuine normalized lambda Kummer pairing of
the two literal global Kummer classes. -/
theorem canonicalRawFullOrbitReadings827_sum_eq_normalizedLambdaPairing :
    (rawFullOrbitReadings827 K
        (canonicalRawPrimal827 K) (canonicalRawReflected827 K)).sum
          (fun _ value ↦ value) =
      normalizedLambdaGlobalPairing59 K
        (strictKummerClass59 K (canonicalRawPrimal827 K))
        (relaxedKummerClass827 K (canonicalRawReflected827 K)) := by
  rw [canonicalRawFullOrbitReadings827_sum_eq_rawWildReading]
  rfl

/-- Representative-level readback of the normalized lambda receipt. -/
theorem canonicalRawFullOrbitReadings827_sum_eq_normalizedLambdaRepresentatives :
    (rawFullOrbitReadings827 K
        (canonicalRawPrimal827 K) (canonicalRawReflected827 K)).sum
          (fun _ value ↦ value) =
      normalizedLambdaGlobalPairing59 K
        (Additive.ofMul (QuotientGroup.mk'
          (powMonoidHom 59 : Kˣ →* Kˣ).range
          (ReflectedQRelaxedLocalizationLift827.primalRepresentative
            (CanonicalPrimalSelmerMode827.canonicalZeta59_isPrimitive K))))
        (Additive.ofMul (QuotientGroup.mk'
          (powMonoidHom 59 : Kˣ →* Kˣ).range
          (canonicalBaseConjugatePairLift827
            (K := K)).candidateRepresentative)) := by
  rw [canonicalRawFullOrbitReadings827_sum_eq_normalizedLambdaPairing,
    canonicalRawPrimal827_kummerClass,
    canonicalRawReflected827_kummerClass]

/-- Therefore reciprocity for this literal generated-unit/conjugate-pair
evaluation is precisely the remaining assertion that its normalized wild
Kummer reading vanishes. -/
theorem canonicalRawFullOrbitReadings827_sum_eq_zero_iff :
    (rawFullOrbitReadings827 K
        (canonicalRawPrimal827 K) (canonicalRawReflected827 K)).sum
          (fun _ value ↦ value) = 0 ↔
      rawWildReading59 K
        (canonicalRawPrimal827 K) (canonicalRawReflected827 K) = 0 := by
  rw [canonicalRawFullOrbitReadings827_sum_eq_rawWildReading]

/-- Away from lambda and the complete 827 orbit, the raw readout and the
canonical tame ledger are both literally zero. -/
theorem canonicalRawFullOrbitReadings827_eq_canonicalLedger_of_outside
    (v : Place K) (hwild : v ≠ lambdaPlace59 K)
    (h827 : v ∉ placesOver827 K) :
    rawFullOrbitReadings827 K
        (canonicalRawPrimal827 K) (canonicalRawReflected827 K) v =
      canonicalTameLedger827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59
        (canonicalBaseConjugatePairLift827 (K := K)) v := by
  rw [rawFullOrbitReadings827_apply_eq_zero_of_outside K _ _ v hwild h827,
    canonicalTameLedger827_apply_eq_zero_of_not_over827
      (K := K) canonicalTeichmullerCharacter59 irregularCharacter59
      (canonicalBaseConjugatePairLift827 (K := K)) v h827]

end Fermat.FiftyNine.Conservation.CanonicalRawConjugatePairReadout827
