/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The canonical residue of the completed logarithm trace at 59

The normalized trace of the genuine completed logarithm was proved integral
and congruent to `-1` modulo `59` in `CompletedLogTraceNonzero59`.  Here we
package that field element itself as a rational 59-adic integer and expose its
canonical residue scalar.

The integer representative is not chosen from an existential witness: its
underlying element is definitionally `normalizedCompletedLogTrace59`; the
existence theorem is used only to prove membership in the valuation ring.
This keeps the construction canonical while recording uniqueness explicitly.
-/
import Fermat.Exponents.FiftyNine.Conservation.CompletedLogTraceNonzero59

open scoped NumberField Topology Valued WithZero

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

namespace Fermat.FiftyNine.Conservation.CompletedLogResidue59

open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59
open Fermat.FiftyNine.Conservation.CompletedLogTraceNonzero59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The canonical rational 59-adic integer represented by the normalized
trace of the genuine completed logarithm.  Its underlying field element is
the trace itself; no witness is selected. -/
def normalizedCompletedLogTrace59Integer : RationalIntegerRing59 := by
  refine ⟨normalizedCompletedLogTrace59 K, ?_⟩
  obtain ⟨z, hz, -⟩ :=
    exists_integer_normalizedCompletedLogTrace59_and_residue K
  rw [hz]
  exact z.property

/-- Coercing the canonical integer representative back to the rational local
field recovers the normalized completed-log trace definitionally. -/
@[simp]
theorem normalizedCompletedLogTrace59Integer_coe :
    ((normalizedCompletedLogTrace59Integer K : RationalIntegerRing59) :
        RationalCompletion59) = normalizedCompletedLogTrace59 K :=
  rfl

/-- The integral representative of the normalized completed-log trace is
unique. -/
theorem normalizedCompletedLogTrace59Integer_unique
    (z : RationalIntegerRing59)
    (hz : (z : RationalCompletion59) = normalizedCompletedLogTrace59 K) :
    z = normalizedCompletedLogTrace59Integer K := by
  apply Subtype.ext
  simpa using hz

/-- The canonical residue scalar read from the normalized completed-log
trace. -/
def normalizedCompletedLogTrace59Residue : ZMod 59 :=
  rationalPadicIntegerToZMod 59 (normalizedCompletedLogTrace59Integer K)

/-- The canonical completed-log residue is exactly `-1` modulo `59`. -/
theorem normalizedCompletedLogTrace59Residue_eq_neg_one :
    normalizedCompletedLogTrace59Residue K = (-1 : ZMod 59) := by
  obtain ⟨z, hz, hres⟩ :=
    exists_integer_normalizedCompletedLogTrace59_and_residue K
  have hcanonical : z = normalizedCompletedLogTrace59Integer K :=
    normalizedCompletedLogTrace59Integer_unique K z hz.symm
  rw [normalizedCompletedLogTrace59Residue, ← hcanonical]
  exact hres

/-- In particular, the canonical completed-log residue is nonzero. -/
theorem normalizedCompletedLogTrace59Residue_ne_zero :
    normalizedCompletedLogTrace59Residue K ≠ 0 := by
  rw [normalizedCompletedLogTrace59Residue_eq_neg_one]
  norm_num

end Fermat.FiftyNine.Conservation.CompletedLogResidue59
