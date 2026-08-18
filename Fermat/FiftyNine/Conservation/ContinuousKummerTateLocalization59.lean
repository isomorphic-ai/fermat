/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Continuous Kummer--Tate pairing at the cyclotomic lambda place

This file specializes the continuous Kummer--Tate coefficient algebra to the
actual completion of the `59`-th cyclotomic field at
`lambda = (zeta_59 - 1)`.  Its retained output is genuine continuous `H^2`
with roots-of-unity coefficients.

The descended cup remains an explicit input so this adapter is independent of
its implementation.  Likewise, scalarization takes a plain linear or
continuous-linear readout as an explicit argument.  No provider structure,
local-invariant existence claim, Tate-duality theorem, Hilbert-symbol
comparison, or new axiom is introduced here.
-/
import Fermat.Conservation.ContinuousKummerTateAlgebra
import Fermat.Conservation.LocalKummerTransport
import Fermat.FiftyNine.Conservation.LocalCompletion59

noncomputable section

namespace Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59

open Fermat.Conservation
open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.ContinuousKummerTateAlgebra
open Fermat.Conservation.LocalKummerTransport
open Fermat.Conservation.TameSymbol
open Fermat.Conservation.WildKummerPairing
open Fermat.FiftyNine.Conservation.LocalCompletion59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- The primitive-root-oriented left seat in continuous local `H^1`. -/
abbrev LambdaOrientedContinuousH1 :=
  OrientedContinuousH1 59 (LambdaLocalField59 K)

/-- The roots-of-unity-valued right seat in continuous local `H^1`. -/
abbrev LambdaRootsContinuousH1 :=
  ContinuousKummerCohomologyOne 59 (LambdaLocalField59 K)

/-- The exact retained target: continuous local `H^2` with `mu_59`
coefficients.  It is neither the oriented trivial-coefficient target nor
ordinary discrete group cohomology. -/
abbrev LambdaRootsContinuousH2 :=
  ContinuousKummerCohomologyTwo 59 (LambdaLocalField59 K)

/-- The exact type of a descended continuous cup at the cyclotomic wild
completion. -/
abbrev LambdaContinuousCup59 :=
  LambdaOrientedContinuousH1 K →ₗ[ZMod 59]
    LambdaRootsContinuousH1 K →ₗ[ZMod 59]
      LambdaRootsContinuousH2 K

/-- The weakest scalar readout seam needed by the downstream algebra.

This is only a type alias for an explicit argument; it does not install or
postulate a local invariant. -/
abbrev LambdaContinuousH2Readout59 :=
  LambdaRootsContinuousH2 K →ₗ[ZMod 59] ZMod 59

/-- The topology-preserving form of the scalar readout seam.

A future normalized local invariant should naturally inhabit this stronger
type.  Its underlying linear map is accepted by the minimal adapter below. -/
abbrev LambdaContinuousH2ContinuousReadout59 :=
  LambdaRootsContinuousH2 K →L[ZMod 59] ZMod 59

/-- Consume a completed continuous cup and the canonical lambda-local Kummer
maps while retaining the honest continuous `H^2(mu_59)` result. -/
def lambdaLocalH2PairingFromCup
    (cup : LambdaContinuousCup59 K) :
    KummerClass 59 (LambdaLocalField59 K) →+
      KummerClass 59 (LambdaLocalField59 K) →+
        LambdaRootsContinuousH2 K :=
  kummerPairingFromCup 59 (LambdaLocalField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K) cup

/-- Readback of the retained local `H^2` pairing. -/
@[simp]
theorem lambdaLocalH2PairingFromCup_apply
    (cup : LambdaContinuousCup59 K)
    (x y : KummerClass 59 (LambdaLocalField59 K)) :
    lambdaLocalH2PairingFromCup K cup x y =
      cup
        (leftKummerMap 59 (LambdaLocalField59 K)
          (lambdaLocalPrimitiveRoot59 K)
          (lambdaLocalPrimitiveRoot59_isPrimitive K) x)
        (rightKummerMap 59 (LambdaLocalField59 K) y) :=
  rfl

/-- Scalarize the retained local `H^2` pairing by an explicitly supplied
linear readout. -/
def lambdaLocalPairingFromCup
    (cup : LambdaContinuousCup59 K)
    (readout : LambdaContinuousH2Readout59 K) :
    WildKummerPairing.Pairing 59 (LambdaLocalField59 K) where
  toFun x := readout.toAddMonoidHom.comp
    (lambdaLocalH2PairingFromCup K cup x)
  map_zero' := by
    ext y
    simp
  map_add' x y := by
    ext z
    simp

/-- Readback of the scalarized local pairing. -/
@[simp]
theorem lambdaLocalPairingFromCup_apply
    (cup : LambdaContinuousCup59 K)
    (readout : LambdaContinuousH2Readout59 K)
    (x y : KummerClass 59 (LambdaLocalField59 K)) :
    lambdaLocalPairingFromCup K cup readout x y =
      readout (cup
        (leftKummerMap 59 (LambdaLocalField59 K)
          (lambdaLocalPrimitiveRoot59 K)
          (lambdaLocalPrimitiveRoot59_isPrimitive K) x)
        (rightKummerMap 59 (LambdaLocalField59 K) y)) :=
  rfl

/-- A topology-preserving readout enters only through its underlying linear
map; this adapter still makes no existence or normalization claim. -/
def lambdaLocalPairingFromContinuousReadout
    (cup : LambdaContinuousCup59 K)
    (readout : LambdaContinuousH2ContinuousReadout59 K) :
    WildKummerPairing.Pairing 59 (LambdaLocalField59 K) :=
  lambdaLocalPairingFromCup K cup readout.toLinearMap

/-- Readback of the topology-preserving scalarization adapter. -/
@[simp]
theorem lambdaLocalPairingFromContinuousReadout_apply
    (cup : LambdaContinuousCup59 K)
    (readout : LambdaContinuousH2ContinuousReadout59 K)
    (x y : KummerClass 59 (LambdaLocalField59 K)) :
    lambdaLocalPairingFromContinuousReadout K cup readout x y =
      readout (cup
        (leftKummerMap 59 (LambdaLocalField59 K)
          (lambdaLocalPrimitiveRoot59 K)
          (lambdaLocalPrimitiveRoot59_isPrimitive K) x)
        (rightKummerMap 59 (LambdaLocalField59 K) y)) :=
  rfl

/-- Pull the scalarized local pairing back to global Kummer classes along the
canonical embedding into the lambda-adic completion. -/
def lambdaGlobalPairingFromCup
    (cup : LambdaContinuousCup59 K)
    (readout : LambdaContinuousH2Readout59 K) :
    WildKummerPairing.Pairing 59 K :=
  LocalKummerTransport.Pairing.pullback (lambdaLocalization59 K)
    (lambdaLocalPairingFromCup K cup readout)

/-- Readback of the global pullback: both Kummer classes are first transported
to the actual lambda-adic completion. -/
@[simp]
theorem lambdaGlobalPairingFromCup_apply
    (cup : LambdaContinuousCup59 K)
    (readout : LambdaContinuousH2Readout59 K)
    (x y : KummerClass 59 K) :
    lambdaGlobalPairingFromCup K cup readout x y =
      readout (cup
        (leftKummerMap 59 (LambdaLocalField59 K)
          (lambdaLocalPrimitiveRoot59 K)
          (lambdaLocalPrimitiveRoot59_isPrimitive K)
          (LocalKummerTransport.map 59 (lambdaLocalization59 K) x))
        (rightKummerMap 59 (LambdaLocalField59 K)
          (LocalKummerTransport.map 59 (lambdaLocalization59 K) y))) :=
  rfl

end Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59
