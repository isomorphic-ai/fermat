/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The complete twisted-lambda cup receipt at 59

The normalized local endpoint already constructs an honest continuous
Kummer cup and proves that its selected normalized readout is one.  This
module retains that result without discarding the two degree-one factors
which created it.

The factor order is deliberate.  The field-valued factor occupies the
oriented left `H¹(F, F_59)` coefficient carrier, while the roots-valued
factor occupies the right `H¹(F, mu_59)` coefficient carrier.  This is the
coefficient variance required by the eventual global
`chi | omega * chi⁻¹` pairing; the factors are not swapped or identified.
It does **not** by itself put either concrete factor in one of those
Delta-character eigenspaces.  In particular, the names `primal` and
`reflected` below record the two roles in the oriented cup, not proved
character-seating laws.  The receipt asserts no new global eigenspace,
localization, Tate-duality, or reciprocity theorem.
-/
import Fermat.Exponents.FiftyNine.Conservation.NormalizedContinuousKummerPairing59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation

open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerOrientation
open ContinuousKummerTateLocalization59
open LocalCompletion59
open NormImageBridge59
open NormalizedContinuousKummerPairing59
open TwistedLambdaKummerCupComparison59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The complete local receipt behind the normalized twisted-lambda
reading.  Its two factors live in distinct coefficient carriers, its
degree-two output is the actual continuous cup class, and the fixed
normalized readout retains both the exact value and its nonvanishing. -/
structure TwistedLambdaCupReceipt59 where
  /-- The field-valued factor in the oriented left Kummer coefficient
  carrier.  No `chi` eigenlaw is asserted here. -/
  primal : LambdaOrientedContinuousH1 K
  /-- The roots-valued factor in the right Kummer coefficient carrier.
  No `omega * chi⁻¹` eigenlaw is asserted here. -/
  reflected : LambdaRootsContinuousH1 K
  /-- The retained roots-of-unity-valued continuous `H²` class. -/
  cupClass : LambdaRootsContinuousH2 K
  /-- The retained class is produced by the actual continuous cup of the
  two retained factors. -/
  cup_eq : lambdaContinuousCup59 K primal reflected = cupClass
  /-- The retained cup class is genuinely nonzero. -/
  cup_ne_zero : cupClass ≠ 0
  /-- The committed normalized readout evaluates the retained class to its
  normalized value. -/
  normalized_reading :
    normalizedInflationReadout59 K cupClass = 1
  /-- In particular, the normalized scalar reading is nonzero. -/
  reading_ne_zero :
    normalizedInflationReadout59 K cupClass ≠ 0

/-- The concrete W1 receipt.  The factors are exactly those occurring in
`twistedLambdaKummerCupH2Class59`; its cup equation is therefore
definitional.  Nonvanishing and normalization are the previously proved
norm-image and normalized-inflation results, not new assumptions. -/
noncomputable def twistedLambdaCupReceipt59 :
    TwistedLambdaCupReceipt59 K where
  primal :=
    orientH1 59 (LambdaLocalField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (continuousClassOfUnit 59 (LambdaLocalField59 K)
        (twistedLambdaRadicandUnit59 K))
  reflected :=
    continuousClassOfUnit 59 (LambdaLocalField59 K)
      (Fermat.Conservation.KummerOrientation.primitiveUnit
        59 (LambdaLocalField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K))
  cupClass := twistedLambdaKummerCupH2Class59 K
  cup_eq := rfl
  cup_ne_zero :=
    twistedLambdaKummerCupH2Class59_ne_zero K
  normalized_reading :=
    normalizedInflationReadout59_twistedLambdaCup K
  reading_ne_zero := by
    rw [normalizedInflationReadout59_twistedLambdaCup K]
    exact one_ne_zero

end Fermat.FiftyNine.Conservation
