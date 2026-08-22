/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# A genuine norm-residue direction for the twisted-lambda Kummer cup

The compatible-root calculation identifies the concrete twisted-lambda
Kummer cup with the explicit pulled carry class.  The generic carry
criterion therefore says that this genuine continuous `H²(mu_59)` class
vanishes exactly when the twisted-lambda Kummer character lifts through
`C_(59²)`.

Albert's already-constructed forward map then proves one honest direction
of the local norm-residue criterion: if the local primitive root is a norm
from the twisted-lambda Kummer extension, the genuine Kummer cup vanishes.
Equivalently, a nonzero cup obstructs every such norm witness.

No local invariant, Hilbert symbol, supplied readout, or comparison formula
is introduced here.  The reverse Albert implication will turn the final
one-way norm statement below into an equivalence.
-/
import Fermat.Experiments.Conservation.ContinuousCarryH2LiftCriterion59
import Fermat.Exponents.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59
import Fermat.Exponents.FiftyNine.Conservation.TwistedLambdaAlbertCriterion59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59

open Fermat.Conservation.ContinuousCarryH2LiftCriterion59
open Fermat.Conservation.ContinuousCarryLiftObstruction59
open Fermat.Conservation.FiniteCyclicH2Generator59
open ContinuousKummerTateLocalization59
open LocalCompletion59
open TwistedLambdaAlbertCriterion59
open TwistedLambdaCarryH2Class59
open TwistedLambdaKummerCupComparison59
open TwistedLambdaKummerQuotient59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The genuine twisted-lambda Kummer cup vanishes exactly when its concrete
Kummer character lifts continuously from `C_59` to `C_(59²)`. -/
theorem twistedLambdaKummerCupH2Class59_eq_zero_iff_exists_continuous_lift :
    twistedLambdaKummerCupH2Class59 K = 0 ↔
      ∃ psi : Field.absoluteGaloisGroup (LambdaField59 K) →ₜ*
          CyclicGroup59Squared,
        reduction59.comp psi = twistedLambdaKummerCharacter59 K := by
  rw [← twistedLambdaRootsCarryH2Class59_eq_kummerCup K]
  rw [← (lambdaH2CoefficientOrientationEquiv59 K).map_eq_zero_iff]
  rw [lambdaH2CoefficientOrientationEquiv59_twistedLambdaRootsCarry]
  exact pulledCarryH2Class59_eq_zero_iff_exists_continuous_lift
    (twistedLambdaKummerCharacter59 K)

/-- Nonvanishing of the genuine twisted-lambda cup is exactly the existing
continuous cyclic-lift obstruction, with no scalar readout chosen. -/
theorem twistedLambdaKummerCupH2Class59_ne_zero_iff_noContinuousLift :
    twistedLambdaKummerCupH2Class59 K ≠ 0 ↔
      TwistedLambdaNoContinuousLift59 K := by
  simpa [TwistedLambdaNoContinuousLift59] using
    not_congr
      (twistedLambdaKummerCupH2Class59_eq_zero_iff_exists_continuous_lift K)

/-- An actual norm witness for the primitive root kills the genuine
twisted-lambda Kummer cup.  This is the forward norm-residue implication. -/
theorem twistedLambdaKummerCupH2Class59_eq_zero_of_primitiveRoot_norm
    (beta : twistedLambdaKummerExtension59 K)
    (hbeta : Algebra.norm (LambdaField59 K) beta =
      lambdaLocalPrimitiveRoot59 K) :
    twistedLambdaKummerCupH2Class59 K = 0 := by
  rw [twistedLambdaKummerCupH2Class59_eq_zero_iff_exists_continuous_lift K]
  obtain ⟨psi, hpsi⟩ :=
    exists_twistedLambdaAlbertCharacter3481_of_norm K beta hbeta
  refine ⟨psi, ?_⟩
  rw [← cyclicReduction3481To59_eq_reduction59]
  exact hpsi

/-- Contrapositively, a surviving genuine Kummer cup excludes every norm
witness for the local primitive root. -/
theorem primitiveRoot_not_norm_of_twistedLambdaKummerCupH2Class59_ne_zero
    (hcup : twistedLambdaKummerCupH2Class59 K ≠ 0)
    (beta : twistedLambdaKummerExtension59 K) :
    Algebra.norm (LambdaField59 K) beta ≠
      lambdaLocalPrimitiveRoot59 K := by
  intro hbeta
  exact hcup
    (twistedLambdaKummerCupH2Class59_eq_zero_of_primitiveRoot_norm
      K beta hbeta)

end Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59
