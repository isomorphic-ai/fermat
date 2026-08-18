/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Continuous Kummer--Tate pairing at the cyclotomic lambda place

This file specializes the continuous Kummer--Tate coefficient algebra to the
actual completion of the `59`-th cyclotomic field at
`lambda = (zeta_59 - 1)`.  Its retained output is genuine continuous `H^2`
with roots-of-unity coefficients.

The reusable adapters retain an explicit descended-cup input, while the
canonical specialization consumes the actual continuous cup.  Scalarization
still takes a plain linear or continuous-linear readout as an explicit
argument.  No provider structure, local-invariant existence claim,
Tate-duality theorem, Hilbert-symbol comparison, or unsupported postulate is
introduced here.
-/
import Fermat.Conservation.ContinuousKummerTateAlgebra
import Fermat.Conservation.LocalKummerTransport
import Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
import Fermat.FiftyNine.Conservation.LocalCompletion59
import Fermat.FiftyNine.Conservation.VostokovLocalization59

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59

open Fermat.Conservation
open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.ContinuousKummerTateAlgebra
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.LocalKummerTransport
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

/-- The same lambda-local degree-two cohomology after changing only the
roots-of-unity coefficients to the primitive-root-oriented trivial line. -/
abbrev LambdaOrientedContinuousH2 :=
  OrientedContinuousH2 59 (LambdaLocalField59 K)

/-- The primitive root at lambda induces an equivalence between the two
coefficient presentations of continuous local `H²`.  This changes
coordinates; it is not a local invariant or scalar readout. -/
def lambdaH2CoefficientOrientationEquiv59 :
    LambdaRootsContinuousH2 K ≃L[ZMod 59]
      LambdaOrientedContinuousH2 K :=
  orientH2Equiv 59 (LambdaLocalField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)

/-- Readback of the lambda-local coefficient orientation through the
underlying continuous linear map. -/
@[simp]
theorem lambdaH2CoefficientOrientationEquiv59_apply
    (x : LambdaRootsContinuousH2 K) :
    lambdaH2CoefficientOrientationEquiv59 K x =
      orientH2 59 (LambdaLocalField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K) x :=
  rfl

/-- The exact type of a descended continuous cup at the cyclotomic wild
completion. -/
abbrev LambdaContinuousCup59 :=
  LambdaOrientedContinuousH1 K →ₗ[ZMod 59]
    LambdaRootsContinuousH1 K →ₗ[ZMod 59]
      LambdaRootsContinuousH2 K

/-- The actual continuous cup specialized to the coefficient pairing at the
cyclotomic lambda completion. -/
def lambdaContinuousCup59 : LambdaContinuousCup59 K :=
  kummerCupH1 59 (LambdaLocalField59 K)

/-- Readback of the canonical lambda-local cup specialization. -/
@[simp]
theorem lambdaContinuousCup59_apply
    (x : LambdaOrientedContinuousH1 K)
    (y : LambdaRootsContinuousH1 K) :
    lambdaContinuousCup59 K x y =
      kummerCupH1 59 (LambdaLocalField59 K) x y :=
  rfl

/-- The weakest scalar readout seam needed by the downstream algebra.

This is only a type alias for an explicit argument; it does not install or
postulate a local invariant. -/
abbrev LambdaContinuousH2Readout59 :=
  LambdaRootsContinuousH2 K →ₗ[ZMod 59] ZMod 59

/-- A supplied nonzero lambda-local `H²` class admits some algebraic linear
readout taking value one on it.

This specialization is conditional and noncanonical: it neither supplies the
class or its nonzero proof nor constructs a continuous readout, normalized
local invariant, or Hilbert-symbol comparison. -/
theorem exists_conditionalNoncanonicalLambdaH2Readout_eq_one
    (z : LambdaRootsContinuousH2 K) (hz : z ≠ 0) :
    ∃ readout : LambdaContinuousH2Readout59 K, readout z = 1 :=
  exists_conditionalNoncanonicalReadout_eq_one
    59 (LambdaLocalField59 K) z hz

/-- Linear scalar readouts written in the oriented `H²` coordinates.  This
is a type of possible supplied maps, not a distinguished local invariant. -/
abbrev LambdaOrientedContinuousH2Readout59 :=
  LambdaOrientedContinuousH2 K →ₗ[ZMod 59] ZMod 59

/-- Losslessly transport a supplied linear readout from oriented `H²`
coordinates to the roots-valued `H²` retained by the canonical cup.  This
equivalence constructs no readout. -/
def lambdaH2SuppliedLinearReadoutTransportEquiv59 :
    LambdaOrientedContinuousH2Readout59 K ≃ₗ[ZMod 59]
      LambdaContinuousH2Readout59 K :=
  orientH2ReadoutEquiv 59 (LambdaLocalField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)

/-- A transported supplied readout first changes the coefficient coordinates
of the retained degree-two class. -/
@[simp]
theorem lambdaH2SuppliedLinearReadoutTransportEquiv59_apply
    (readout : LambdaOrientedContinuousH2Readout59 K)
    (x : LambdaRootsContinuousH2 K) :
    lambdaH2SuppliedLinearReadoutTransportEquiv59 K readout x =
      readout (lambdaH2CoefficientOrientationEquiv59 K x) :=
  rfl

/-- Inverse transport evaluates a roots-valued supplied readout after the
inverse coefficient orientation. -/
@[simp]
theorem lambdaH2SuppliedLinearReadoutTransportEquiv59_symm_apply
    (readout : LambdaContinuousH2Readout59 K)
    (x : LambdaOrientedContinuousH2 K) :
    (lambdaH2SuppliedLinearReadoutTransportEquiv59 K).symm readout x =
      readout ((lambdaH2CoefficientOrientationEquiv59 K).symm x) :=
  rfl

/-- The topology-preserving form of the scalar readout seam.

A future normalized local invariant should naturally inhabit this stronger
type.  Its underlying linear map is accepted by the minimal adapter below. -/
abbrev LambdaContinuousH2ContinuousReadout59 :=
  LambdaRootsContinuousH2 K →L[ZMod 59] ZMod 59

/-- Topology-preserving scalar readouts written in the oriented `H²`
coordinates.  This is again only a type of explicitly supplied maps. -/
abbrev LambdaOrientedContinuousH2ContinuousReadout59 :=
  LambdaOrientedContinuousH2 K →L[ZMod 59] ZMod 59

/-- Losslessly transport a supplied topology-preserving readout from
oriented `H²` coordinates to roots-valued `H²`.  The equivalence contains no
chosen invariant, normalization, or arithmetic value. -/
def lambdaH2SuppliedContinuousReadoutTransportEquiv59 :
    LambdaOrientedContinuousH2ContinuousReadout59 K ≃ₗ[ZMod 59]
      LambdaContinuousH2ContinuousReadout59 K :=
  orientH2ContinuousReadoutEquiv 59 (LambdaLocalField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)

/-- Application of the transported supplied continuous readout. -/
@[simp]
theorem lambdaH2SuppliedContinuousReadoutTransportEquiv59_apply
    (readout : LambdaOrientedContinuousH2ContinuousReadout59 K)
    (x : LambdaRootsContinuousH2 K) :
    lambdaH2SuppliedContinuousReadoutTransportEquiv59 K readout x =
      readout (lambdaH2CoefficientOrientationEquiv59 K x) :=
  rfl

/-- Inverse application of the supplied continuous-readout transport. -/
@[simp]
theorem lambdaH2SuppliedContinuousReadoutTransportEquiv59_symm_apply
    (readout : LambdaContinuousH2ContinuousReadout59 K)
    (x : LambdaOrientedContinuousH2 K) :
    (lambdaH2SuppliedContinuousReadoutTransportEquiv59 K).symm readout x =
      readout ((lambdaH2CoefficientOrientationEquiv59 K).symm x) :=
  rfl

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

/-- Apply the canonical continuous cup to the canonical lambda-local Kummer
maps, retaining the honest roots-of-unity-valued continuous `H²` class. -/
def lambdaLocalH2Pairing :
    KummerClass 59 (LambdaLocalField59 K) →+
      KummerClass 59 (LambdaLocalField59 K) →+
        LambdaRootsContinuousH2 K :=
  kummerPairing 59 (LambdaLocalField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)

/-- Readback of the canonical retained local `H²` pairing. -/
@[simp]
theorem lambdaLocalH2Pairing_apply
    (x y : KummerClass 59 (LambdaLocalField59 K)) :
    lambdaLocalH2Pairing K x y =
      lambdaContinuousCup59 K
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

/-- Scalarize the canonical retained local `H²` pairing by an explicitly
supplied linear readout. -/
def lambdaLocalPairing
    (readout : LambdaContinuousH2Readout59 K) :
    WildKummerPairing.Pairing 59 (LambdaLocalField59 K) :=
  lambdaLocalPairingFromCup K (lambdaContinuousCup59 K) readout

/-- Readback of the canonical scalarized local pairing. -/
@[simp]
theorem lambdaLocalPairing_apply
    (readout : LambdaContinuousH2Readout59 K)
    (x y : KummerClass 59 (LambdaLocalField59 K)) :
    lambdaLocalPairing K readout x y =
      readout (lambdaContinuousCup59 K
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

/-- Scalarize the canonical local cup by an explicitly supplied
topology-preserving readout. -/
def lambdaLocalPairingWithContinuousReadout
    (readout : LambdaContinuousH2ContinuousReadout59 K) :
    WildKummerPairing.Pairing 59 (LambdaLocalField59 K) :=
  lambdaLocalPairingFromContinuousReadout K
    (lambdaContinuousCup59 K) readout

/-- Readback of the canonical topology-preserving scalarization. -/
@[simp]
theorem lambdaLocalPairingWithContinuousReadout_apply
    (readout : LambdaContinuousH2ContinuousReadout59 K)
    (x y : KummerClass 59 (LambdaLocalField59 K)) :
    lambdaLocalPairingWithContinuousReadout K readout x y =
      readout (lambdaContinuousCup59 K
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

/-- Pull the canonical scalarized lambda-local pairing back to global Kummer
classes.  The scalar readout remains explicit. -/
def lambdaGlobalPairing
    (readout : LambdaContinuousH2Readout59 K) :
    WildKummerPairing.Pairing 59 K :=
  lambdaGlobalPairingFromCup K (lambdaContinuousCup59 K) readout

/-- Readback of the canonical global pullback. -/
@[simp]
theorem lambdaGlobalPairing_apply
    (readout : LambdaContinuousH2Readout59 K)
    (x y : KummerClass 59 K) :
    lambdaGlobalPairing K readout x y =
      readout (lambdaContinuousCup59 K
        (leftKummerMap 59 (LambdaLocalField59 K)
          (lambdaLocalPrimitiveRoot59 K)
          (lambdaLocalPrimitiveRoot59_isPrimitive K)
          (LocalKummerTransport.map 59 (lambdaLocalization59 K) x))
        (rightKummerMap 59 (LambdaLocalField59 K)
          (LocalKummerTransport.map 59 (lambdaLocalization59 K) y))) :=
  rfl

section CanonicalCore

variable (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
variable (wild : OldWildInterface59
  (cyclotomicStrictSelmerRepresentation59 K) omega chi (lambdaPlace59 K))

/-- The canonical-action 59-core built from the genuine continuous local cup.

The lambda place, completion, primitive root, two continuous Kummer maps,
global pullback, and strict-to-827-relaxed landing are all derived.  Once the
existing characters and old wild interface are fixed, the only arithmetic
inputs are an explicit `H²(mu_59)` readout and an independent comparison of
the resulting Kummer pairing with the old reading. -/
def toCanonicalReflectedWildKummerCoreAt59
    (readout : LambdaContinuousH2Readout59 K)
    (hcalibration :
      ∀ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi,
      ∀ y : OldReflectedDual59
        (cyclotomicStrictSelmerRepresentation59 K) omega chi,
        lambdaGlobalPairing K readout (toKummerClass x) (toKummerClass y) =
          wild.reading x y) :
    ReflectedWildKummerCoreAt59
      (cyclotomicStrictSelmerRepresentation59 K)
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi (lambdaPlace59 K) wild where
  pairing := lambdaGlobalPairing K readout
  landing := cyclotomicReflectedEmptySupportLanding827 K omega chi
  old_calibration := hcalibration

@[simp]
theorem toCanonicalReflectedWildKummerCoreAt59_pairing_apply
    (readout : LambdaContinuousH2Readout59 K)
    (hcalibration :
      ∀ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi,
      ∀ y : OldReflectedDual59
        (cyclotomicStrictSelmerRepresentation59 K) omega chi,
        lambdaGlobalPairing K readout (toKummerClass x) (toKummerClass y) =
          wild.reading x y)
    (x y : KummerClass 59 K) :
    (toCanonicalReflectedWildKummerCoreAt59 K omega chi wild readout
      hcalibration).pairing x y = lambdaGlobalPairing K readout x y :=
  rfl

end CanonicalCore

end Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59
