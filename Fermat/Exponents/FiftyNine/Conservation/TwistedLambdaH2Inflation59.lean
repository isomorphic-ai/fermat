/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Inflate the normalized cyclic H² class to the twisted-lambda Kummer cup

Pullback along the concrete twisted-lambda Kummer character sends trivial
`F_59`-valued continuous `H²` on `C_59` to oriented continuous `H²` on the
local absolute Galois group.  Inverse coefficient orientation then lands in
the roots-of-unity coefficients retained by the genuine Kummer cup.

The resulting linear map sends the canonical normalized finite carry class
literally to the genuine twisted-lambda Kummer cup.  Thus the remaining
normalization requirement for a future local invariant is one exact linear
map equality, not a choice of a value on a single class.  No local invariant,
Hilbert symbol, readout provider, or reciprocity formula is introduced here.
-/
import Fermat.Experiments.Conservation.ContinuousH2Pullback59
import Fermat.Exponents.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59

open ContinuousCohomology
open Fermat.Conservation.ContinuousCarryLiftObstruction59
open Fermat.Conservation.ContinuousCyclicH2Readout59
open Fermat.Conservation.ContinuousH2Pullback59
open Fermat.Conservation.CyclicCarryH2Class59
open Fermat.Conservation.FiniteCyclicH2Generator59
open ContinuousKummerTateLocalization59
open LocalCompletion59
open TwistedLambdaCarryH2Class59
open TwistedLambdaKummerCupComparison59
open TwistedLambdaKummerQuotient59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- Pull continuous `H²(C_59,F_59)` to the concrete local absolute Galois
group and change from oriented trivial coefficients to `mu_59`. -/
noncomputable def twistedLambdaH2Inflation59 :
    (continuousCohomology
        (ZMod 59) CyclicGroup59 2).obj continuousCoefficients59 →ₗ[ZMod 59]
      LambdaRootsContinuousH2 K :=
  (lambdaH2CoefficientOrientationEquiv59 K).symm.toLinearMap.comp
    (pullbackActualContinuousH2 (twistedLambdaKummerCharacter59 K))

/-- The normalized finite carry generator inflates literally to the genuine
twisted-lambda Kummer cup. -/
@[simp]
theorem twistedLambdaH2Inflation59_continuousCarryH2Class59 :
    twistedLambdaH2Inflation59 K continuousCarryH2Class59 =
      twistedLambdaKummerCupH2Class59 K := by
  rw [twistedLambdaH2Inflation59]
  change (lambdaH2CoefficientOrientationEquiv59 K).symm
      (pullbackActualContinuousH2 (twistedLambdaKummerCharacter59 K)
        continuousCarryH2Class59) = _
  rw [pullbackActualContinuousH2_continuousCarryH2Class59]
  change (lambdaH2CoefficientOrientationEquiv59 K).symm
      (pulledCarryH2Class59 (twistedLambdaKummerCharacter59 K)) = _
  change twistedLambdaRootsCarryH2Class59 K = _
  exact twistedLambdaRootsCarryH2Class59_eq_kummerCup K

/-- Any local roots-valued readout whose restriction along the genuine
inflation map is the normalized finite-cyclic readout sends the concrete
Kummer cup to exactly one. -/
theorem readout_twistedLambdaKummerCupH2Class59_eq_one_of_normalized_inflation
    (readout : LambdaRootsContinuousH2 K →ₗ[ZMod 59] ZMod 59)
    (hnormalized :
      readout.comp (twistedLambdaH2Inflation59 K) =
        actualContinuousCyclicH2Readout59) :
    readout (twistedLambdaKummerCupH2Class59 K) = 1 := by
  rw [← twistedLambdaH2Inflation59_continuousCarryH2Class59 K]
  change (readout.comp (twistedLambdaH2Inflation59 K))
      continuousCarryH2Class59 = 1
  rw [hnormalized]
  exact actualContinuousCyclicH2Readout59_continuousCarryH2Class59

end Fermat.FiftyNine.Conservation.TwistedLambdaH2Inflation59
