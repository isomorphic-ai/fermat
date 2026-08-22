/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Unconditional normalized continuous Kummer pairing at 59

The norm-image theorem supplies, by ordinary linear algebra, a noncanonical
algebraic readout on the genuine continuous local `H²(mu_59)` target.  This
file selects one such readout and composes it with the actual continuous cup
product.  It thereby constructs total local and global Kummer pairings and
proves their normalization on the twisted-lambda and unit-60 classes.

The cup product and retained cohomology are continuous.  The selected scalar
readout is a plain linear map; no continuity of that readout is claimed.  The
only input left by the adapter to an independently supplied historical wild
interface is the explicit reciprocity/calibration comparison.
-/
import Fermat.Exponents.FiftyNine.Conservation.NormImageConsequences59
import Fermat.Exponents.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59
import Fermat.Exponents.FiftyNine.Conservation.TwistedLambdaNormalizationSign59
import Mathlib.Tactic

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59

open Fermat.Conservation
open Fermat.Conservation.ContinuousCyclicH2Readout59
open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.LocalKummerTransport
open Fermat.Conservation.TameSymbol
open Fermat.Conservation.WildKummerPairing
open Fermat.Conservation.SelmerEigenspace
open CompletedLogResidue59
open ContinuousKummerTateLocalization59
open CyclotomicSelmerAction59
open DetectorWitness827
open LocalCompletion59
open NormImageConsequences59
open SplitPrimeFourier827
open TwistedLambdaCupUnitReduction59
open TwistedLambdaH2Inflation59
open TwistedLambdaKummerCupComparison59
open TwistedLambdaNormalizationSign59
open TwistedLambdaKummerQuotient59
open UlamReadout827
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- A noncanonical but unconditional algebraic readout, selected from the
proved normalized-inflation existence theorem. -/
noncomputable def normalizedInflationReadout59 :
    LambdaContinuousH2Readout59 K :=
  Classical.choose (exists_normalizedInflationReadout59 K)

/-- The selected readout retains the full normalized-inflation equation. -/
theorem normalizedInflationReadout59_comp :
    (normalizedInflationReadout59 K).comp (twistedLambdaH2Inflation59 K) =
      actualContinuousCyclicH2Readout59 :=
  Classical.choose_spec (exists_normalizedInflationReadout59 K)

/-- The selected readout sends the genuine twisted-lambda Kummer cup to one. -/
theorem normalizedInflationReadout59_twistedLambdaCup :
    normalizedInflationReadout59 K (twistedLambdaKummerCupH2Class59 K) = 1 :=
  readout_twistedLambdaKummerCupH2Class59_eq_one_of_normalized_inflation
    K (normalizedInflationReadout59 K) (normalizedInflationReadout59_comp K)

/-- The same readout sends the genuine unit-60 cup to one. -/
theorem normalizedInflationReadout59_unit60Cup :
    normalizedInflationReadout59 K (unit60KummerCupH2Class59 K) = 1 := by
  rw [← twistedLambdaKummerCupH2Class59_eq_unit60KummerCupH2Class59 K]
  exact normalizedInflationReadout59_twistedLambdaCup K

/-- The normalized value is also the negative completed-log residue. -/
theorem normalizedInflationReadout59_twistedLambdaCup_eq_neg_logResidue :
    normalizedInflationReadout59 K (twistedLambdaKummerCupH2Class59 K) =
      -normalizedCompletedLogTrace59Residue K :=
  normalizedReadout_twistedLambdaKummerCup_eq_neg_completedLogResidue
    K (normalizedInflationReadout59 K) (normalizedInflationReadout59_comp K)

/-- Total local Kummer pairing obtained from the actual continuous cup and
the unconditionally selected normalized algebraic readout. -/
noncomputable def normalizedLambdaLocalPairing59 :
    Pairing 59 (LambdaField59 K) :=
  lambdaLocalPairing K (normalizedInflationReadout59 K)

/-- Total global pairing obtained by pulling the normalized local pairing
back along the actual lambda-adic completion embedding. -/
noncomputable def normalizedLambdaGlobalPairing59 : Pairing 59 K :=
  lambdaGlobalPairing K (normalizedInflationReadout59 K)

@[simp]
theorem normalizedLambdaLocalPairing59_apply
    (x y : KummerClass 59 (LambdaField59 K)) :
    normalizedLambdaLocalPairing59 K x y =
      normalizedInflationReadout59 K
        (lambdaLocalH2Pairing K x y) :=
  rfl

@[simp]
theorem normalizedLambdaGlobalPairing59_apply
    (x y : KummerClass 59 K) :
    normalizedLambdaGlobalPairing59 K x y =
      normalizedLambdaLocalPairing59 K
        (Fermat.Conservation.LocalKummerTransport.map 59
          (lambdaLocalization59 K) x)
      (Fermat.Conservation.LocalKummerTransport.map 59
          (lambdaLocalization59 K) y) :=
  rfl

/-- The global element `60 * (zeta_59 - 1)`, bundled as a nonzero unit before
transport to the lambda-adic completion. -/
def globalTwistedLambdaRadicandUnit59 : Kˣ :=
  Units.mk0 ((60 : K) * (globalPrimitiveRoot59 K - 1))
    (mul_ne_zero (by norm_num)
      (sub_ne_zero.mpr
        ((globalPrimitiveRoot59_isPrimitive K).ne_one (by norm_num))))

/-- The global unit `60`, bundled before lambda-adic transport. -/
def globalUnit60RadicandUnit59 : Kˣ :=
  Units.mk0 (60 : K) (by norm_num)

/-- Localization of the explicit global twisted-lambda representative is the
genuine local twisted-lambda representative. -/
@[simp]
theorem unitMap_globalTwistedLambdaRadicandUnit59 :
    Fermat.Conservation.LocalKummerTransport.unitMap
        (lambdaLocalization59 K) (globalTwistedLambdaRadicandUnit59 K) =
      twistedLambdaRadicandUnit59 K := by
  apply Units.ext
  simp [globalTwistedLambdaRadicandUnit59, twistedLambdaRadicandUnit59,
    Fermat.Conservation.KummerCharacterComparison59.radicandUnit59,
    TwistedLambdaKummerQuotient59.twistedLambda59,
    TwistedLambdaKummerQuotient59.twistUnit59,
    TwistedLambdaKummerQuotient59.canonicalLambda59,
    LocalCompletion59.lambdaLocalPrimitiveRoot59,
    LocalCompletion59.localPrimitiveRoot59,
    LocalCompletion59.lambdaLocalization59,
    LocalCompletion59.localization59]

/-- Localization of the global unit `60` is the genuine local unit-60
representative. -/
@[simp]
theorem unitMap_globalUnit60RadicandUnit59 :
    Fermat.Conservation.LocalKummerTransport.unitMap
        (lambdaLocalization59 K) (globalUnit60RadicandUnit59 K) =
      unit60RadicandUnit59 K := by
  apply Units.ext
  rfl

/-- Localization also preserves the selected cyclotomic primitive unit. -/
@[simp]
theorem unitMap_globalPrimitiveUnit59 :
    Fermat.Conservation.LocalKummerTransport.unitMap
        (lambdaLocalization59 K)
        (Fermat.Conservation.KummerOrientation.primitiveUnit 59 K
          (globalPrimitiveRoot59 K)
          (globalPrimitiveRoot59_isPrimitive K)) =
      Fermat.Conservation.KummerOrientation.primitiveUnit
        59 (LambdaField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K) := by
  apply Units.ext
  rfl

/-- The total local pairing has normalized value one on the genuine
twisted-lambda class against the selected primitive-root class. -/
theorem normalizedLambdaLocalPairing59_twistedLambda_primitive :
    normalizedLambdaLocalPairing59 K
        (classOfUnit 59 (LambdaField59 K)
          (Additive.ofMul (twistedLambdaRadicandUnit59 K)))
        (classOfUnit 59 (LambdaField59 K)
          (Additive.ofMul (Fermat.Conservation.KummerOrientation.primitiveUnit
            59 (LambdaField59 K)
            (lambdaLocalPrimitiveRoot59 K)
            (lambdaLocalPrimitiveRoot59_isPrimitive K)))) = 1 := by
  rw [normalizedLambdaLocalPairing59, lambdaLocalPairing_apply]
  simp only [classOfUnit_apply, leftKummerMap_classOfUnit,
    rightKummerMap_classOfUnit]
  exact normalizedInflationReadout59_twistedLambdaCup K

/-- The total local pairing has the same normalized value on the genuine
principal-unit class of 60. -/
theorem normalizedLambdaLocalPairing59_unit60_primitive :
    normalizedLambdaLocalPairing59 K
        (classOfUnit 59 (LambdaField59 K)
          (Additive.ofMul (unit60RadicandUnit59 K)))
        (classOfUnit 59 (LambdaField59 K)
          (Additive.ofMul (Fermat.Conservation.KummerOrientation.primitiveUnit
            59 (LambdaField59 K)
            (lambdaLocalPrimitiveRoot59 K)
            (lambdaLocalPrimitiveRoot59_isPrimitive K)))) = 1 := by
  rw [normalizedLambdaLocalPairing59, lambdaLocalPairing_apply]
  simp only [classOfUnit_apply, leftKummerMap_classOfUnit,
    rightKummerMap_classOfUnit]
  exact normalizedInflationReadout59_unit60Cup K

/-- The global pullback has normalized value one on the explicit global
twisted-lambda representative against the global primitive root. -/
theorem normalizedLambdaGlobalPairing59_twistedLambda_primitive :
    normalizedLambdaGlobalPairing59 K
        (classOfUnit 59 K
          (Additive.ofMul (globalTwistedLambdaRadicandUnit59 K)))
        (classOfUnit 59 K
          (Additive.ofMul (Fermat.Conservation.KummerOrientation.primitiveUnit
            59 K (globalPrimitiveRoot59 K)
            (globalPrimitiveRoot59_isPrimitive K)))) = 1 := by
  rw [normalizedLambdaGlobalPairing59_apply]
  simp only [Fermat.Conservation.LocalKummerTransport.map_classOfUnit,
    unitMap_globalTwistedLambdaRadicandUnit59,
    unitMap_globalPrimitiveUnit59]
  exact normalizedLambdaLocalPairing59_twistedLambda_primitive K

/-- The global pullback likewise has normalized value one on the global
unit-60 representative against the global primitive root. -/
theorem normalizedLambdaGlobalPairing59_unit60_primitive :
    normalizedLambdaGlobalPairing59 K
        (classOfUnit 59 K
          (Additive.ofMul (globalUnit60RadicandUnit59 K)))
        (classOfUnit 59 K
          (Additive.ofMul (Fermat.Conservation.KummerOrientation.primitiveUnit
            59 K (globalPrimitiveRoot59 K)
            (globalPrimitiveRoot59_isPrimitive K)))) = 1 := by
  rw [normalizedLambdaGlobalPairing59_apply]
  simp only [Fermat.Conservation.LocalKummerTransport.map_classOfUnit,
    unitMap_globalUnit60RadicandUnit59,
    unitMap_globalPrimitiveUnit59]
  exact normalizedLambdaLocalPairing59_unit60_primitive K

section ExistingWildInterface

variable (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
variable (wild : OldWildInterface59
  (cyclotomicStrictSelmerRepresentation59 K) omega chi (lambdaPlace59 K))

/-- Install the unconditional normalized Kummer--Tate pairing in the existing
reflected-wild core once its value is compared with the independently supplied
old wild reading.  The canonical strict-to-827-relaxed landing is derived by
the underlying localization adapter. -/
noncomputable def toNormalizedReflectedWildKummerCoreAt59
    (hcalibration :
      ∀ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi,
      ∀ y : OldReflectedDual59
        (cyclotomicStrictSelmerRepresentation59 K) omega chi,
        normalizedLambdaGlobalPairing59 K
            (toKummerClass x) (toKummerClass y) = wild.reading x y) :
    ReflectedWildKummerCoreAt59
      (cyclotomicStrictSelmerRepresentation59 K)
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi (lambdaPlace59 K) wild :=
  ContinuousKummerTateLocalization59.toCanonicalReflectedWildKummerCoreAt59
    K omega chi wild (normalizedInflationReadout59 K) hcalibration

@[simp]
theorem toNormalizedReflectedWildKummerCoreAt59_pairing_apply
    (hcalibration :
      ∀ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi,
      ∀ y : OldReflectedDual59
        (cyclotomicStrictSelmerRepresentation59 K) omega chi,
        normalizedLambdaGlobalPairing59 K
            (toKummerClass x) (toKummerClass y) = wild.reading x y)
    (x y : KummerClass 59 K) :
    (toNormalizedReflectedWildKummerCoreAt59 K omega chi wild
      hcalibration).pairing x y = normalizedLambdaGlobalPairing59 K x y :=
  rfl

end ExistingWildInterface

end Fermat.FiftyNine.Conservation.NormalizedContinuousKummerPairing59
