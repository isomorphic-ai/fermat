/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The conditional normalized twisted-lambda endpoint at 59

Let a concrete roots-valued local continuous `H²` readout be given.  The
only compatibility required here is the exact linear-map naturality equation
saying that its composite with the genuine twisted-lambda inflation is the
already normalized finite-cyclic readout.

From that one visible seam, the genuine twisted-lambda Kummer cup reads as
`1`, hence as the negative of the independently computed completed-log
residue.  It follows that the cup is nonzero, that the local primitive root is
not a norm from the concrete Kummer extension, and that the concrete Kummer
character has no continuous `C_(59²)` lift.

This is an honest conditional composition theorem.  It neither constructs
the local readout nor hides the remaining naturality equation in a provider,
and it introduces no local-invariant or Hilbert-symbol assertion.
-/
import Fermat.FiftyNine.Conservation.TwistedLambdaNormalizationSign59
import Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.TwistedLambdaNormalizedEndpoint59

open Fermat.Conservation.ContinuousCyclicH2Readout59
open ContinuousKummerTateLocalization59
open CompletedLogResidue59
open LocalCompletion59
open TwistedLambdaCarryH2Class59
open TwistedLambdaH2Inflation59
open TwistedLambdaKummerCupComparison59
open TwistedLambdaKummerLiftCriterion59
open TwistedLambdaKummerNormCriterion59
open TwistedLambdaKummerQuotient59
open TwistedLambdaNormalizationSign59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- A normalized local roots-valued readout makes the genuine twisted-lambda
Kummer cup nonzero.  The normalization premise is an equality of the full
linear maps, rather than a stipulated value on the cup. -/
theorem twistedLambdaKummerCupH2Class59_ne_zero_of_normalized_readout
    (readout : LambdaRootsContinuousH2 K →ₗ[ZMod 59] ZMod 59)
    (hnormalized :
      readout.comp (twistedLambdaH2Inflation59 K) =
        actualContinuousCyclicH2Readout59) :
    twistedLambdaKummerCupH2Class59 K ≠ 0 := by
  have hread : readout (twistedLambdaKummerCupH2Class59 K) = 1 :=
    readout_twistedLambdaKummerCupH2Class59_eq_one_of_normalized_inflation
      K readout hnormalized
  intro hzero
  have hscalar := congrArg readout hzero
  rw [map_zero, hread] at hscalar
  exact one_ne_zero hscalar

/-- The complete conditional endpoint.  Its sole non-structural hypothesis
is the explicit normalized-inflation naturality equation displayed below. -/
theorem normalizedReadout_twistedLambdaEndpoint59
    (readout : LambdaRootsContinuousH2 K →ₗ[ZMod 59] ZMod 59)
    (hnormalized :
      readout.comp (twistedLambdaH2Inflation59 K) =
        actualContinuousCyclicH2Readout59) :
    readout (twistedLambdaKummerCupH2Class59 K) = 1 ∧
      readout (twistedLambdaKummerCupH2Class59 K) =
        -normalizedCompletedLogTrace59Residue K ∧
      twistedLambdaKummerCupH2Class59 K ≠ 0 ∧
      (¬ ∃ beta : twistedLambdaKummerExtension59 K,
        Algebra.norm (LambdaField59 K) beta =
          lambdaLocalPrimitiveRoot59 K) ∧
      TwistedLambdaNoContinuousLift59 K := by
  have hreadOne :
      readout (twistedLambdaKummerCupH2Class59 K) = 1 :=
    readout_twistedLambdaKummerCupH2Class59_eq_one_of_normalized_inflation
      K readout hnormalized
  have hreadResidue :
      readout (twistedLambdaKummerCupH2Class59 K) =
        -normalizedCompletedLogTrace59Residue K :=
    normalizedReadout_twistedLambdaKummerCup_eq_neg_completedLogResidue
      K readout hnormalized
  have hcup : twistedLambdaKummerCupH2Class59 K ≠ 0 :=
    twistedLambdaKummerCupH2Class59_ne_zero_of_normalized_readout
      K readout hnormalized
  have hnotNorm :
      ¬ ∃ beta : twistedLambdaKummerExtension59 K,
        Algebra.norm (LambdaField59 K) beta =
          lambdaLocalPrimitiveRoot59 K :=
    (twistedLambdaKummerCupH2Class59_ne_zero_iff_primitiveRoot_not_norm K).mp
      hcup
  have hnolift : TwistedLambdaNoContinuousLift59 K :=
    (twistedLambdaKummerCupH2Class59_ne_zero_iff_noContinuousLift K).mp hcup
  exact ⟨hreadOne, hreadResidue, hcup, hnotNorm, hnolift⟩

end Fermat.FiftyNine.Conservation.TwistedLambdaNormalizedEndpoint59
