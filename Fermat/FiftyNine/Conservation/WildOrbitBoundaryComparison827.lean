/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The wild and full-orbit boundaries on one genuine Selmer test space

The normalized lambda pairing and the complete globally-root-oriented
`827` orbit were previously exposed pointwise on the same seated Selmer
inputs.  This module curries both readings into literal linear functionals
on the actual primal `chi`-Selmer space and identifies the orbit functional
with the restriction of the genuine unseated strict-Selmer functional.

Thus the normalized reflected fiber constructed from the canonical pointed
incidence really does feed both sides of one map-level boundary equation.
If global reciprocity for the already constructed full-orbit pairing is
available, the two functionals are exact negatives, have the same kernel,
and occupy one explicit one-dimensional line whenever either is nonzero.

This is the strongest bridge currently obtainable from the existing
infrastructure.  It does not identify a point of the normalized fiber with
the fixed reflected factor retained by `TwistedLambdaCupReceipt59`; it does
not prove reciprocity or nonvanishing on the seated primal test space; and
it does not manufacture a lambda-plus-827 Poitou--Tate theorem.
-/
import Fermat.Conservation.OneDimensionalUnitProportionality
import Fermat.FiftyNine.Conservation.NormalizedFullOrbitGlobalRealization827
import Fermat.FiftyNine.Conservation.SeatedTameOrbitReciprocityBalance827
import Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827
import Fermat.FiftyNine.Conservation.TwistedLambdaCupReceipt59

open scoped BigOperators MonoidAlgebra NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827

open Fermat.Conservation
open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.LocalKummerTransport
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TameSymbol
open Fermat.Conservation.TatePairing
open Fermat.Conservation.WildKummerPairing
open ArbitraryUnitRawTameCarrierBridge827
open CanonicalConjugatePairIncidence827
open CanonicalFullOrbitLocalPairing827
open CanonicalIrregularMode827
open ContinuousKummerTateLocalization59
open CyclotomicSelmerAction59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open LocalCompletion59
open NormalizedContinuousKummerPairing59
open NormalizedFullOrbitGlobalRealization827
open SeatedTameOrbitReciprocityBalance827
open SplitPrimeFourier827
open StrictTameOrbitClassFactorization827
open TwistedLambdaCupReceipt59
open UlamReadout827
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
private theorem oldPrimal59_nsmul_eq_zero
    (chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi) :
    59 • x = 0 := by
  apply Subtype.ext
  exact SelmerEigenspace.p_nsmul_eq_zero x.1

noncomputable local instance instOldPrimal59ModuleZMod
    (chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    Module (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi) :=
  AddCommGroup.zmodModule (oldPrimal59_nsmul_eq_zero chi)

/-! ## The exact W1 factor landing -/

/-- The oriented left `H¹` factor obtained by localizing a genuine global
Kummer class at lambda. -/
noncomputable def lambdaPrimalFactorOfGlobalKummer59
    (x : KummerClass 59 K) : LambdaOrientedContinuousH1 K :=
  leftKummerMap 59 (LambdaLocalField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)
    (LocalKummerTransport.map 59 (lambdaLocalization59 K) x)

/-- The roots-valued right `H¹` factor obtained by localizing a genuine
global Kummer class at lambda.  Equality of this value with W1's retained
reflected factor is the exact local compatibility required of a future
lambda-plus-827 Poitou--Tate lift. -/
noncomputable def lambdaReflectedFactorOfGlobalKummer59
    (y : KummerClass 59 K) : LambdaRootsContinuousH1 K :=
  rightKummerMap 59 (LambdaLocalField59 K)
    (LocalKummerTransport.map 59 (lambdaLocalization59 K) y)

/-- The global twisted-lambda representative localizes to the exact primal
factor retained by W1, not merely to a class with the same scalar reading. -/
theorem lambdaPrimalFactorOfGlobalTwistedLambda59_eq_receipt :
    lambdaPrimalFactorOfGlobalKummer59 (K := K)
        (classOfUnit 59 K
          (Additive.ofMul (globalTwistedLambdaRadicandUnit59 K))) =
      (twistedLambdaCupReceipt59 K).primal := by
  rw [lambdaPrimalFactorOfGlobalKummer59,
    LocalKummerTransport.map_classOfUnit,
    unitMap_globalTwistedLambdaRadicandUnit59]
  rfl

/-- The global primitive root localizes to the exact reflected factor
retained by W1. -/
theorem lambdaReflectedFactorOfGlobalPrimitive59_eq_receipt :
    lambdaReflectedFactorOfGlobalKummer59 (K := K)
        (classOfUnit 59 K
          (Additive.ofMul
            (Fermat.Conservation.KummerOrientation.primitiveUnit
              59 K (globalPrimitiveRoot59 K)
              (globalPrimitiveRoot59_isPrimitive K)))) =
      (twistedLambdaCupReceipt59 K).reflected := by
  rw [lambdaReflectedFactorOfGlobalKummer59,
    LocalKummerTransport.map_classOfUnit,
    unitMap_globalPrimitiveUnit59]
  rfl

/-- After genuine global-to-local transport, the two explicit global
representatives reproduce W1's retained `H²` cup class exactly. -/
theorem localizedGlobalTwistedLambdaPrimitiveCup59_eq_receipt :
    lambdaContinuousCup59 K
        (lambdaPrimalFactorOfGlobalKummer59 (K := K)
          (classOfUnit 59 K
            (Additive.ofMul (globalTwistedLambdaRadicandUnit59 K))))
        (lambdaReflectedFactorOfGlobalKummer59 (K := K)
          (classOfUnit 59 K
            (Additive.ofMul
              (Fermat.Conservation.KummerOrientation.primitiveUnit
                59 K (globalPrimitiveRoot59 K)
                (globalPrimitiveRoot59_isPrimitive K))))) =
      (twistedLambdaCupReceipt59 K).cupClass := by
  rw [lambdaPrimalFactorOfGlobalTwistedLambda59_eq_receipt,
    lambdaReflectedFactorOfGlobalPrimitive59_eq_receipt]
  exact (twistedLambdaCupReceipt59 K).cup_eq

/-- The exact transported W1 cup retains its proved normalized value one. -/
theorem localizedGlobalTwistedLambdaPrimitiveReading59_eq_one :
    normalizedInflationReadout59 K
        (lambdaContinuousCup59 K
          (lambdaPrimalFactorOfGlobalKummer59 (K := K)
            (classOfUnit 59 K
              (Additive.ofMul (globalTwistedLambdaRadicandUnit59 K))))
          (lambdaReflectedFactorOfGlobalKummer59 (K := K)
            (classOfUnit 59 K
              (Additive.ofMul
                (Fermat.Conservation.KummerOrientation.primitiveUnit
                  59 K (globalPrimitiveRoot59 K)
                  (globalPrimitiveRoot59_isPrimitive K)))))) = 1 := by
  rw [localizedGlobalTwistedLambdaPrimitiveCup59_eq_receipt]
  exact (twistedLambdaCupReceipt59 K).normalized_reading

/-- The normalized global pairing is literally the retained continuous cup
of the two localized degree-one factors. -/
theorem normalizedLambdaGlobalPairing59_eq_localized_factor_cup
    (x y : KummerClass 59 K) :
    normalizedLambdaGlobalPairing59 K x y =
      normalizedInflationReadout59 K
        (lambdaContinuousCup59 K
          (lambdaPrimalFactorOfGlobalKummer59 (K := K) x)
          (lambdaReflectedFactorOfGlobalKummer59 (K := K) y)) :=
  rfl

/-- Fixing one actual reflected q-relaxed class curries the normalized
lambda-local Kummer pairing into a linear functional on the genuine seated
primal Selmer space. -/
noncomputable def seatedWildBoundaryFunctional59
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    Module.Dual (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi) :=
  (((rawWildReading59 K).flip y.1).comp
    (toSeatedCarrier
      (rho := cyclotomicStrictSelmerRepresentation59 K)
      (chi := chi)).toAddMonoidHom).toZModLinearMap 59

/-- Fixing the same reflected class curries the sum of all 58 genuine tame
rows into a linear functional on exactly the same primal space. -/
noncomputable def seatedOrbitBoundaryFunctional827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    Module.Dual (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi) :=
  ((∑ tau : GaloisIndex59,
      ((rawTameOrbitReading827 K tau).flip y.1).comp
        (toSeatedCarrier
          (rho := cyclotomicStrictSelmerRepresentation59 K)
          (chi := chi)).toAddMonoidHom)).toZModLinearMap 59

@[simp]
theorem seatedWildBoundaryFunctional59_apply
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi) :
    seatedWildBoundaryFunctional59 (K := K) omega chi y x =
      normalizedLambdaGlobalPairing59 K
        (toKummerClass x) (toKummerClassAt y) :=
  rfl

/-- If an actual reflected q-relaxed class has W1's prescribed lambda-local
factor, then its wild boundary is exactly the W1-reflected cup functional on
every seated primal Selmer test.  This is an implication from a literal
localization equality, not a supplied provider structure. -/
theorem seatedWildBoundaryFunctional59_eq_receipt_cup_of_localizes
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (hlocal :
      lambdaReflectedFactorOfGlobalKummer59 (K := K)
          (toKummerClassAt y) =
        (twistedLambdaCupReceipt59 K).reflected)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi) :
    seatedWildBoundaryFunctional59 (K := K) omega chi y x =
      normalizedInflationReadout59 K
        (lambdaContinuousCup59 K
          (lambdaPrimalFactorOfGlobalKummer59 (K := K) (toKummerClass x))
          (twistedLambdaCupReceipt59 K).reflected) := by
  rw [seatedWildBoundaryFunctional59_apply,
    normalizedLambdaGlobalPairing59_eq_localized_factor_cup, hlocal]

@[simp]
theorem seatedOrbitBoundaryFunctional827_apply
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi) :
    seatedOrbitBoundaryFunctional827 (K := K) omega chi y x =
      seatedTameOrbitSum827 K omega chi x y := by
  rfl

/-- The seated orbit boundary is literally the already constructed genuine
strict-Selmer orbit functional restricted to the `chi` eigenspace. -/
theorem seatedOrbitBoundaryFunctional827_eq_strictTameOrbitFunctional827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi) :
    seatedOrbitBoundaryFunctional827 (K := K) omega chi y x =
      strictTameOrbitFunctional827 K y.1 x.1 := by
  rw [seatedOrbitBoundaryFunctional827_apply,
    strictTameOrbitFunctional827_apply]
  rfl

/-- Global reciprocity for the actual full-orbit pairing is exactly a
map-level cancellation between the normalized lambda boundary and the full
`827` boundary. -/
theorem seatedWildBoundaryFunctional59_add_orbit_eq_zero
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K omega chi))
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    seatedWildBoundaryFunctional59 (K := K) omega chi y +
        seatedOrbitBoundaryFunctional827 (K := K) omega chi y = 0 := by
  ext x
  simp only [LinearMap.add_apply, LinearMap.zero_apply,
    seatedWildBoundaryFunctional59_apply,
    seatedOrbitBoundaryFunctional827_apply]
  rw [seatedTameOrbitSum827_eq_neg_normalizedLambda_of_globalReciprocity
    K omega chi reciprocity x y]
  exact add_neg_cancel _

/-- Equivalent oriented spelling of the map-level reciprocity balance. -/
theorem seatedWildBoundaryFunctional59_eq_neg_orbit
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K omega chi))
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    seatedWildBoundaryFunctional59 (K := K) omega chi y =
      -seatedOrbitBoundaryFunctional827 (K := K) omega chi y := by
  exact eq_neg_of_add_eq_zero_left
    (seatedWildBoundaryFunctional59_add_orbit_eq_zero
      omega chi reciprocity y)

/-- Under reciprocity the two genuine boundary maps have exactly the same
kernel on the seated primal Selmer test space. -/
theorem seatedWildBoundaryFunctional59_ker_eq_orbit_ker
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K omega chi))
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    (seatedWildBoundaryFunctional59 (K := K) omega chi y).ker =
      (seatedOrbitBoundaryFunctional827 (K := K) omega chi y).ker := by
  rw [seatedWildBoundaryFunctional59_eq_neg_orbit
    omega chi reciprocity y]
  ext x
  simp

/-- The explicit common line generated by the orbit boundary.  This is not
claimed to contain the wild boundary without a comparison theorem. -/
noncomputable def wildOrbitCommonLine827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    Submodule (ZMod 59)
      (Module.Dual (ZMod 59)
        (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)) :=
  ZMod 59 ∙ seatedOrbitBoundaryFunctional827 (K := K) omega chi y

theorem seatedOrbitBoundaryFunctional827_mem_commonLine
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    seatedOrbitBoundaryFunctional827 (K := K) omega chi y ∈
      wildOrbitCommonLine827 (K := K) omega chi y :=
  Submodule.mem_span_singleton_self _

theorem seatedWildBoundaryFunctional59_mem_commonLine_of_reciprocity
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K omega chi))
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    seatedWildBoundaryFunctional59 (K := K) omega chi y ∈
      wildOrbitCommonLine827 (K := K) omega chi y := by
  rw [seatedWildBoundaryFunctional59_eq_neg_orbit
    omega chi reciprocity y]
  exact Submodule.neg_mem _
    (seatedOrbitBoundaryFunctional827_mem_commonLine omega chi y)

theorem wildOrbitCommonLine827_finrank_eq_one
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (horbit : seatedOrbitBoundaryFunctional827 (K := K) omega chi y ≠ 0) :
    Module.finrank (ZMod 59)
      (wildOrbitCommonLine827 (K := K) omega chi y) = 1 :=
  finrank_span_singleton horbit

/-- Once one actual boundary is nonzero, the generic W4 linear algebra now
applies to the two concrete maps.  Reciprocity provides their common-line
comparison; it does not provide the nonzero seated value. -/
theorem existsUnique_unit_wild_eq_smul_orbit_of_reciprocity
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K omega chi))
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (horbit : seatedOrbitBoundaryFunctional827 (K := K) omega chi y ≠ 0) :
    ∃! u : (ZMod 59)ˣ,
      seatedWildBoundaryFunctional59 (K := K) omega chi y =
        (u : ZMod 59) •
          seatedOrbitBoundaryFunctional827 (K := K) omega chi y := by
  have hwild : seatedWildBoundaryFunctional59 (K := K) omega chi y ≠ 0 := by
    rw [seatedWildBoundaryFunctional59_eq_neg_orbit
      omega chi reciprocity y]
    exact neg_ne_zero.mpr horbit
  exact existsUnique_unit_smul_of_mem_finrank_one
    (wildOrbitCommonLine827 (K := K) omega chi y)
    (seatedWildBoundaryFunctional59 (K := K) omega chi y)
    (seatedOrbitBoundaryFunctional827 (K := K) omega chi y)
    (seatedWildBoundaryFunctional59_mem_commonLine_of_reciprocity
      omega chi reciprocity y)
    (seatedOrbitBoundaryFunctional827_mem_commonLine omega chi y)
    (wildOrbitCommonLine827_finrank_eq_one omega chi y horbit)
    hwild horbit

/-- The canonical pointed-incidence construction supplies a genuine
normalized reflected fiber point, and that same point simultaneously feeds
the normalized lambda functional and the genuine full-orbit functional.
The existential retains the whole fiber discipline: no point is named. -/
theorem exists_normalized_wildOrbitBoundaryPair827 :
    ∃ y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)),
      (∀ tau : GaloisIndex59,
        relaxedOrbitValuation827 K tau y.1.1 =
          normalizedFullOrbitEigenprofileCoordinates827
            canonicalTeichmullerCharacter59 irregularCharacter59 tau) ∧
      (∀ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59,
        seatedOrbitBoundaryFunctional827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59 y.1 x =
          strictTameOrbitFunctional827 K y.1.1 x.1) := by
  obtain ⟨y⟩ :=
    canonicalConjugatePairNormalizedReflectedFiber827_nonempty (K := K)
  refine ⟨y, ?_, ?_⟩
  · intro tau
    exact normalizedReflectedFiber827_relaxedOrbitValuation_eq_profile
      canonicalTeichmullerCharacter59 irregularCharacter59 y tau
  · intro x
    exact seatedOrbitBoundaryFunctional827_eq_strictTameOrbitFunctional827
      canonicalTeichmullerCharacter59 irregularCharacter59 y.1 x

end Fermat.FiftyNine.Conservation.WildOrbitBoundaryComparison827
