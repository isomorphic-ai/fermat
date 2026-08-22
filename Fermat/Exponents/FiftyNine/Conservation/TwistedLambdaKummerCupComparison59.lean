/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The twisted-lambda carry is the genuine Kummer cup at 59

This module specializes the compatible Kummer lift at 59 to the concrete
`60 * (zeta_59 - 1)` radicand in the lambda-adic completion.  The existing
splitting-field Kummer character is identified with the genuine oriented
Kummer character of that radicand.  The unconditional carry/cup bridge then
identifies the campaign's oriented carry class with the genuine local Kummer
cup, and injectivity of coefficient orientation gives the same equality in
the retained roots-of-unity-valued continuous `H²`.
-/
import Fermat.Experiments.Conservation.CompatibleKummerLift59
import Fermat.Experiments.Conservation.KummerCharacterComparison59
import Fermat.Exponents.FiftyNine.Conservation.TwistedLambdaCarryH2Class59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59

open Fermat.Conservation.CompatibleKummerLift59
open Fermat.Conservation.ContinuousCarryLiftObstruction59
open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.ContinuousKummerTateAlgebra
open Fermat.Conservation.KummerCharacterComparison59
open Fermat.Conservation.KummerOrientation
open Fermat.Conservation.OrientedCarryH2Class59
open Fermat.Conservation.OrientedKummerRepresentative59
open ContinuousKummerTateLocalization59
open LocalCompletion59
open TwistedLambdaCarryH2Class59
open TwistedLambdaKummerQuotient59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The nonzero twisted-lambda radicand bundled as a unit in the completed
local field. -/
def twistedLambdaRadicandUnit59 : (LambdaField59 K)ˣ :=
  radicandUnit59 (LambdaField59 K) (twistedLambda59 K)
    (twistedLambda59_not_pow K)

/-- The existing splitting-field Kummer character is exactly the genuine
oriented chosen-root Kummer character of the same twisted radicand. -/
theorem twistedLambdaKummerCharacter59_eq_orientedKummerCharacter :
    twistedLambdaKummerCharacter59 K =
      orientedKummerCharacter (LambdaField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K)
        (twistedLambdaRadicandUnit59 K) := by
  simpa [twistedLambdaKummerCharacter59, twistedLambdaRadicandUnit59] using
    (kummerCharacter59_eq_orientedKummerCharacter
      (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (twistedLambda59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (twistedLambda59_not_pow K))

/-- The genuine lambda-local Kummer cup of the twisted radicand against the
cyclotomic primitive unit. -/
def twistedLambdaKummerCupH2Class59 : LambdaRootsContinuousH2 K :=
  lambdaContinuousCup59 K
    (orientH1 59 (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (continuousClassOfUnit 59 (LambdaField59 K)
        (twistedLambdaRadicandUnit59 K)))
    (continuousClassOfUnit 59 (LambdaField59 K)
      (primitiveUnit 59 (LambdaField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K)))

/-- In oriented coefficients, the concrete twisted-lambda carry is exactly
the coefficient orientation of the genuine twisted-lambda Kummer cup. -/
theorem twistedLambdaOrientedCarry_eq_orientedKummerCup :
    twistedLambdaOrientedCarryH2Class59 K =
      lambdaH2CoefficientOrientationEquiv59 K
        (twistedLambdaKummerCupH2Class59 K) := by
  have h := pulledCarry_actualH2_eq_orientedKummerCup
    (LambdaField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)
    (twistedLambdaRadicandUnit59 K)
  rw [← twistedLambdaKummerCharacter59_eq_orientedKummerCharacter K] at h
  exact h

/-- Removing the lossless coefficient orientation identifies the existing
roots-valued carry class with the genuine lambda-local Kummer cup. -/
theorem twistedLambdaRootsCarryH2Class59_eq_kummerCup :
    twistedLambdaRootsCarryH2Class59 K =
      twistedLambdaKummerCupH2Class59 K := by
  apply (lambdaH2CoefficientOrientationEquiv59 K).injective
  rw [lambdaH2CoefficientOrientationEquiv59_twistedLambdaRootsCarry]
  exact twistedLambdaOrientedCarry_eq_orientedKummerCup K

end Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59
