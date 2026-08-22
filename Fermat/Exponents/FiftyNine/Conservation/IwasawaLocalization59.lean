/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Adapt a total Iwasawa trace product to the 59-local wild core

This file performs only the instance-layer wiring.  A total augmented
trace-product formula supplies the representative pairing.  Ambient action
compatibility supplies the canonical empty-support landing.  The remaining
calibration is stated on the literal chosen representatives found by the C1
shape audit and is supplied as an independent theorem.

In particular, the pairing is never defined from the old wild reading.  No
section, complement, or product decomposition of the strict and q-relaxed
carriers is introduced.
-/
import Fermat.Experiments.Conservation.IwasawaTracePairing
import Fermat.Exponents.FiftyNine.Conservation.VostokovShapeAudit59

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.IwasawaLocalization59

open Fermat.Conservation
open Fermat.Conservation.IwasawaTracePairing
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.WildKummerPairing
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.UlamReadout827
open Fermat.FiftyNine.Conservation.VostokovLocalization59
open Fermat.FiftyNine.Conservation.VostokovShapeAudit59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  {A : Type*} [Ring A]
  (rho : SelmerDeltaRepresentation
    (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
    (Delta := GaloisIndex59))
  (rhoQ : QRelaxedSelmerDeltaRepresentation827 K GaloisIndex59)
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
  (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers K))
  (wild : OldWildInterface59 rho omega chi distinguishedPlace)

/-- The calibrated tier-(c) reduction for the literal C1 representatives.

The right representative is chosen only after applying the canonical
strict-to-q-relaxed inclusion obtained from ambient action compatibility.
`Reduction.comparison` is therefore the independent arithmetic calibration
theorem; neither the representative pairing nor its coordinates are defined
from `wild.reading`.  This type identifies no carriers and chooses no
splitting between them. -/
abbrev CalibratedReductionAt59
    (compatibility : EmptySupportActionCompatibility827 rho rhoQ) :=
  IwasawaTracePairing.Reduction 59 K A
    (fun x : OldPrimal59 rho chi ↦
      Additive.ofMul (statewiseRepresentative rho chi x))
    (fun y : OldReflectedDual59 rho omega chi ↦
      Additive.ofMul
        (transverseRepresentative rhoQ omega chi
          (oldReflectedToQRelaxed827 rho rhoQ omega chi
            (EmptySupportActionCompatibility827.toReflectedLanding
              rho rhoQ omega chi compatibility) y)))
    (fun x y ↦ wild.reading x y)

omit [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Representative calibration implies calibration of the canonical Kummer
descent on the old carriers.

This is a theorem from the two C1 readback receipts.  It is not a definition
of the trace-product formula from `wild.reading`. -/
theorem descend_eq_oldReading
    (compatibility : EmptySupportActionCompatibility827 rho rhoQ)
    (reduction : CalibratedReductionAt59 (A := A) rho rhoQ omega chi
      distinguishedPlace wild compatibility)
    (x : OldPrimal59 rho chi)
    (y : OldReflectedDual59 rho omega chi) :
    reduction.representative.descend (toKummerClass x) (toKummerClass y) =
      wild.reading x y := by
  let landing : ReflectedEmptySupportLanding827 rho rhoQ omega chi :=
    EmptySupportActionCompatibility827.toReflectedLanding
      rho rhoQ omega chi compatibility
  let included : QRelaxedReflectedDual827 rhoQ omega chi :=
    oldReflectedToQRelaxed827 rho rhoQ omega chi landing y
  have hleft :
      toKummerClass x =
        classOfUnit 59 K
          (Additive.ofMul (statewiseRepresentative rho chi x)) := by
    simpa [classOfUnit, statewiseKummerClass,
      statewiseRepresentative] using
      (statewiseRepresentative_readback rho chi x).symm
  have hright :
      toKummerClass y =
        classOfUnit 59 K
          (Additive.ofMul
            (transverseRepresentative rhoQ omega chi included)) := by
    rw [← toKummerClassAt_oldReflectedToQRelaxed827
      rho rhoQ omega chi landing y]
    change transverseKummerClass rhoQ omega chi included = _
    simpa [classOfUnit, transverseRepresentative] using
      (transverseRepresentative_readback rhoQ omega chi included).symm
  rw [hleft, hright,
    RepresentativePairing.descend_classOfUnit_classOfUnit]
  exact reduction.representative_eq_reading x y

/-- Package a total Iwasawa trace-product formula and its two independent
instance receipts as the complete strict wild Kummer core at 59. -/
def toReflectedWildKummerCoreAt59
    (compatibility : EmptySupportActionCompatibility827 rho rhoQ)
    (reduction : CalibratedReductionAt59 (A := A) rho rhoQ omega chi
      distinguishedPlace wild compatibility) :
    ReflectedWildKummerCoreAt59 rho rhoQ omega chi
      distinguishedPlace wild where
  pairing := reduction.representative.descend
  landing := EmptySupportActionCompatibility827.toReflectedLanding
    rho rhoQ omega chi compatibility
  old_calibration := descend_eq_oldReading rho rhoQ omega chi
    distinguishedPlace wild compatibility reduction

/-- Fire the complete reflected wild-localization producer directly from a
calibrated Iwasawa reduction and ambient action compatibility. -/
def toReflectedWildLocalizationAt59
    (compatibility : EmptySupportActionCompatibility827 rho rhoQ)
    (reduction : CalibratedReductionAt59 (A := A) rho rhoQ omega chi
      distinguishedPlace wild compatibility) :
    UlamReadout827.ReflectedWildLocalizationAt59
      (Place := IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))
      (SelmerChi := OldPrimal59 rho chi)
      (DOmegaSelmerChiStar := OldReflectedDual59 rho omega chi)
      rhoQ omega chi distinguishedPlace wild :=
  (toReflectedWildKummerCoreAt59 rho rhoQ omega chi distinguishedPlace wild
    compatibility reduction).toReflectedWildLocalizationAt59

end Fermat.FiftyNine.Conservation.IwasawaLocalization59
