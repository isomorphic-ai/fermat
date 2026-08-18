/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The sign between the two normalized scalar endpoints at 59

The canonical finite-cyclic `H²` readout sends the carry generator to `1`.
Independently, the genuine completed-log trace has canonical residue `-1`.
This module records that the two scalars agree after one explicit negation.

For any local roots-valued `H²` readout whose composition with the genuine
twisted-lambda inflation is the normalized finite readout, the concrete
Kummer cup therefore reads as the negative completed-log residue.

This is a sign-calibration receipt between already computed endpoints.  It
does not prove that the completed-log expression constructs the local
invariant, does not assert a Hilbert-symbol formula, and does not discharge
the remaining reciprocity/naturality theorem.
-/
import Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59
import Fermat.FiftyNine.Conservation.CompletedLogResidue59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.TwistedLambdaNormalizationSign59

open Fermat.Conservation.ContinuousCyclicH2Readout59
open Fermat.Conservation.CyclicCarryH2Class59
open ContinuousKummerTateLocalization59
open CompletedLogResidue59
open TwistedLambdaH2Inflation59
open TwistedLambdaKummerCupComparison59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The negative of the canonical completed-log residue is one. -/
theorem neg_normalizedCompletedLogTrace59Residue_eq_one :
    -normalizedCompletedLogTrace59Residue K = (1 : ZMod 59) := by
  rw [normalizedCompletedLogTrace59Residue_eq_neg_one]
  simp

/-- Exact scalar sign relation between the normalized finite carry readout
and the independently computed completed-log residue. -/
theorem finiteCarryReadout_eq_neg_normalizedCompletedLogTrace59Residue :
    actualContinuousCyclicH2Readout59 continuousCarryH2Class59 =
      -normalizedCompletedLogTrace59Residue K := by
  rw [actualContinuousCyclicH2Readout59_continuousCarryH2Class59]
  symm
  exact neg_normalizedCompletedLogTrace59Residue_eq_one K

/-- Once a local readout satisfies the exact normalized-inflation naturality
equation, its value on the genuine Kummer cup equals the negative canonical
completed-log residue.  The premise remains the visible reciprocity seam. -/
theorem normalizedReadout_twistedLambdaKummerCup_eq_neg_completedLogResidue
    (readout : LambdaRootsContinuousH2 K →ₗ[ZMod 59] ZMod 59)
    (hnormalized :
      readout.comp (twistedLambdaH2Inflation59 K) =
        actualContinuousCyclicH2Readout59) :
    readout (twistedLambdaKummerCupH2Class59 K) =
      -normalizedCompletedLogTrace59Residue K := by
  rw [readout_twistedLambdaKummerCupH2Class59_eq_one_of_normalized_inflation
    K readout hnormalized]
  symm
  exact neg_normalizedCompletedLogTrace59Residue_eq_one K

end Fermat.FiftyNine.Conservation.TwistedLambdaNormalizationSign59
