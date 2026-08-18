/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The twisted-lambda carry class in local Kummer H2

This file applies the explicit carry construction to the concrete
60-twisted lambda Kummer character and transports the resulting actual
continuous H2 class into the roots-of-unity coefficients retained by the
canonical lambda-local Kummer cup.

All nonvanishing and readout statements remain conditional on the single
honest arithmetic proposition that this specified character has no
continuous C59-squared lift.  No such witness, local invariant, or
Bockstein/cup comparison is postulated here.
-/
import Fermat.Conservation.OrientedCarryH2Class59
import Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59
import Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.TwistedLambdaCarryH2Class59

open Fermat.Conservation.ContinuousCarryLiftObstruction59
open Fermat.Conservation.OrientedCarryH2Class59
open ContinuousKummerTateLocalization59
open LocalCompletion59
open TwistedLambdaKummerQuotient59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The exact remaining arithmetic proposition for the specified
60-twisted lambda character. -/
abbrev TwistedLambdaNoContinuousLift59 : Prop :=
  NoContinuousLift (twistedLambdaKummerCharacter59 K)

/-- The explicit pulled carry class in oriented trivial coefficients. -/
def twistedLambdaOrientedCarryH2Class59 :
    LambdaOrientedContinuousH2 K :=
  orientedCarryH2Class59 (LambdaLocalField59 K)
    (twistedLambdaKummerCharacter59 K)

/-- The same actual class in the roots-of-unity coefficients retained by
the canonical lambda-local Kummer cup. -/
def twistedLambdaRootsCarryH2Class59 :
    LambdaRootsContinuousH2 K :=
  rootsCarryH2Class59
    (LambdaLocalField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)
    (twistedLambdaKummerCharacter59 K)

/-- Coefficient orientation reads the roots-valued class back as the
original pulled carry class. -/
@[simp]
theorem lambdaH2CoefficientOrientationEquiv59_twistedLambdaRootsCarry :
    lambdaH2CoefficientOrientationEquiv59 K
        (twistedLambdaRootsCarryH2Class59 K) =
      twistedLambdaOrientedCarryH2Class59 K := by
  exact orientH2Equiv_rootsCarryH2Class59
    (LambdaLocalField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)
    (twistedLambdaKummerCharacter59 K)

/-- The explicit no-lift witness makes the oriented local H2 class
nonzero. -/
theorem twistedLambdaOrientedCarryH2Class59_ne_zero
    (hnolift : TwistedLambdaNoContinuousLift59 K) :
    twistedLambdaOrientedCarryH2Class59 K ≠ 0 :=
  orientedCarryH2Class59_ne_zero_of_noContinuousLift
    (LambdaLocalField59 K) (twistedLambdaKummerCharacter59 K) hnolift

/-- The same no-lift witness produces a nonzero roots-valued actual local
continuous H2 class. -/
theorem twistedLambdaRootsCarryH2Class59_ne_zero
    (hnolift : TwistedLambdaNoContinuousLift59 K) :
    twistedLambdaRootsCarryH2Class59 K ≠ 0 :=
  rootsCarryH2Class59_ne_zero_of_noContinuousLift
    (LambdaLocalField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)
    (twistedLambdaKummerCharacter59 K) hnolift

/-- Once the explicit no-lift arithmetic is proved, ordinary linear algebra
supplies a noncanonical readout taking value one on the surviving class.
This is not the normalized local invariant. -/
theorem exists_twistedLambdaNoncanonicalReadout_eq_one
    (hnolift : TwistedLambdaNoContinuousLift59 K) :
    ∃ readout : LambdaContinuousH2Readout59 K,
      readout (twistedLambdaRootsCarryH2Class59 K) = 1 :=
  exists_conditionalNoncanonicalLambdaH2Readout_eq_one K
    (twistedLambdaRootsCarryH2Class59 K)
    (twistedLambdaRootsCarryH2Class59_ne_zero K hnolift)

end Fermat.FiftyNine.Conservation.TwistedLambdaCarryH2Class59
