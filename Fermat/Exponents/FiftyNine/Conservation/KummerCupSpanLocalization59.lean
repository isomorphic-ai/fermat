/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The Kummer cup span at the actual cyclotomic lambda place

This file installs the span-restricted discrete Kummer--Tate readout at the
literal cyclotomic place `lambda = (zeta_59 - 1)`.  The local field,
localization map, primitive root, and both Kummer maps are all derived from
the cyclotomic number field.  Only a linear readout on the span of the cup
classes that those two Kummer maps actually produce remains as local input.

Pullback along the completion embedding gives a pairing on global Kummer
classes.  The canonical cyclotomic strict-to-827-relaxed landing then installs
that pairing in `ReflectedWildKummerCoreAt59`; the only other arithmetic seam
is an independent calibration against the pre-existing old wild reading.

The readout in this file is deliberately *not* identified with the normalized
continuous local invariant.  Establishing that comparison requires continuous
local cohomology and local duality infrastructure not asserted here.
-/
import Fermat.Experiments.Conservation.KummerCupSpanReadout
import Fermat.Experiments.Conservation.LocalKummerTransport
import Fermat.Exponents.FiftyNine.Conservation.CyclotomicSelmerAction59
import Fermat.Exponents.FiftyNine.Conservation.LocalCompletion59
import Fermat.Exponents.FiftyNine.Conservation.VostokovLocalization59

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59

open groupCohomology
open Fermat.Conservation
open Fermat.Conservation.KummerCupSpanReadout
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TameSymbol
open Fermat.Conservation.WildKummerPairing
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.UlamReadout827
open Fermat.FiftyNine.Conservation.VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- The exact part of discrete degree-two cohomology visited by the two
genuine Kummer maps over the cyclotomic lambda-adic completion. -/
abbrev LambdaKummerCupSpan59 :=
  KummerCupSpanReadout.discreteCupSpan
    (LambdaLocalField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)

/-- The sole local scalar input retained by this adapter: a linear readout on
the actual Kummer cup span, rather than on all discrete `H²`. -/
abbrev LambdaKummerCupSpanReadout59 :=
  LambdaKummerCupSpan59 K →ₗ[ZMod 59] ZMod 59

/-- The span-restricted pairing on the actual lambda-adic completion. -/
def lambdaLocalPairing
    (readout : LambdaKummerCupSpanReadout59 K) :
    WildKummerPairing.Pairing 59 (LambdaLocalField59 K) :=
  KummerCupSpanReadout.discretePairing
    (LambdaLocalField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)
    readout

/-- Pull the lambda-local span-restricted pairing back to global Kummer
classes along the canonical completion embedding. -/
def pairing
    (readout : LambdaKummerCupSpanReadout59 K) :
    WildKummerPairing.Pairing 59 K :=
  LocalKummerTransport.Pairing.pullback
    (lambdaLocalization59 K) (lambdaLocalPairing K readout)

/-- Quotient-level readback.  Both inputs are first transported to the actual
lambda-adic Kummer quotient and then passed through the genuine Kummer maps. -/
@[simp]
theorem pairing_apply
    (readout : LambdaKummerCupSpanReadout59 K)
    (x y : KummerClass 59 K) :
    pairing K readout x y =
      readout
        (KummerCupSpanReadout.cupInSpan
          (LocalKummerH1.rootsRepresentation 59 (LambdaLocalField59 K))
          (KummerOrientation.leftKummerMap 59 (LambdaLocalField59 K)
            (lambdaLocalPrimitiveRoot59 K)
            (lambdaLocalPrimitiveRoot59_isPrimitive K))
          (LocalKummerH1.map 59 (LambdaLocalField59 K))
          (LocalKummerTransport.map 59 (lambdaLocalization59 K) x)
          (LocalKummerTransport.map 59 (lambdaLocalization59 K) y)) :=
  rfl

/-- Representative-level readback.  It exposes the localized units, the
oriented left Kummer class, the right Kummer class, their degree-two cup
receipt, and finally the span-restricted scalar readout. -/
@[simp]
theorem pairing_classOfUnit
    (readout : LambdaKummerCupSpanReadout59 K)
    (a b : Kˣ) :
    pairing K readout
        (WildKummerPairing.classOfUnit 59 K (Additive.ofMul a))
        (WildKummerPairing.classOfUnit 59 K (Additive.ofMul b)) =
      readout
        (KummerCupSpanReadout.cupInSpan
          (LocalKummerH1.rootsRepresentation 59 (LambdaLocalField59 K))
          (KummerOrientation.leftKummerMap 59 (LambdaLocalField59 K)
            (lambdaLocalPrimitiveRoot59 K)
            (lambdaLocalPrimitiveRoot59_isPrimitive K))
          (LocalKummerH1.map 59 (LambdaLocalField59 K))
          (WildKummerPairing.classOfUnit 59 (LambdaLocalField59 K)
            (Additive.ofMul
              (LocalKummerTransport.unitMap (lambdaLocalization59 K) a)))
          (WildKummerPairing.classOfUnit 59 (LambdaLocalField59 K)
            (Additive.ofMul
              (LocalKummerTransport.unitMap (lambdaLocalization59 K) b)))) :=
  rfl

section CanonicalCore

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
variable (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
variable (wild : OldWildInterface59
  (cyclotomicStrictSelmerRepresentation59 K) omega chi (lambdaPlace59 K))

/-- The canonical-action 59-core at the actual cyclotomic lambda place.

The lambda place, completion, primitive root, two Kummer maps, and
strict-to-relaxed landing are derived.  Consequently, after the already
existing characters and old interface are fixed, its only inputs are the
span readout and an independent calibration of that new reading against the
old one. -/
def toCanonicalReflectedWildKummerCoreAt59
    (readout : LambdaKummerCupSpanReadout59 K)
    (hcalibration :
      ∀ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi,
      ∀ y : OldReflectedDual59
        (cyclotomicStrictSelmerRepresentation59 K) omega chi,
        pairing K readout (toKummerClass x) (toKummerClass y) =
          wild.reading x y) :
    ReflectedWildKummerCoreAt59
      (cyclotomicStrictSelmerRepresentation59 K)
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi (lambdaPlace59 K) wild where
  pairing := pairing K readout
  landing := cyclotomicReflectedEmptySupportLanding827 K omega chi
  old_calibration := hcalibration

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem toCanonicalReflectedWildKummerCoreAt59_pairing_apply
    (readout : LambdaKummerCupSpanReadout59 K)
    (hcalibration :
      ∀ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi,
      ∀ y : OldReflectedDual59
        (cyclotomicStrictSelmerRepresentation59 K) omega chi,
        pairing K readout (toKummerClass x) (toKummerClass y) =
          wild.reading x y)
    (x y : KummerClass 59 K) :
    (toCanonicalReflectedWildKummerCoreAt59 K omega chi wild readout
      hcalibration).pairing x y = pairing K readout x y :=
  rfl

end CanonicalCore

end Fermat.FiftyNine.Conservation.KummerCupSpanLocalization59
