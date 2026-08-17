/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Feed the cohomological Kummer--Tate pairing into the 59-local core

This is the instance-layer adapter from the generic cohomological assembly to
the real 59-local consumer.  Localization, both Kummer maps, and the local
invariant construct the quotient pairing.  The empty-support landing and the
independent calibration theorem remain visibly separate inputs.
-/
import Fermat.Conservation.DiscreteKummerTatePairing
import Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
import Fermat.FiftyNine.Conservation.LocalCompletion59
import Fermat.FiftyNine.Conservation.VostokovLocalization59

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.KummerTateLocalization59

open groupCohomology
open Fermat.Conservation
open Fermat.Conservation.CohomologicalKummerPairing
open Fermat.Conservation.DiscreteKummerTatePairing
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TameSymbol
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.UlamReadout827
open Fermat.FiftyNine.Conservation.VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K F G : Type}
  [Field K] [NumberField K] [IsCyclotomicExtension {59} ℚ K]
  [Field F] [Group G]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  (A : Rep (ZMod 59) G)
  (rho : SelmerDeltaRepresentation (R := 𝓞 K) (K := K) (p := 59)
    (Delta := GaloisIndex59))
  (rhoQ : QRelaxedSelmerDeltaRepresentation827 K GaloisIndex59)
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
  (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (wild : OldWildInterface59 rho omega chi distinguishedPlace)

/-- Construct the actual quotient-level pairing produced by the local
Kummer--Tate chain and pull it back along localization. -/
def pairing
    (localization : K →+* F)
    (leftKummer : KummerClass 59 F →+
      H1 (KummerTateCup.trivialLine (k := ZMod 59) (G := G)))
    (rightKummer : KummerClass 59 F →+ H1 A)
    (localInvariant : H2 A →ₗ[ZMod 59] ZMod 59) :
    WildKummerPairing.Pairing 59 K :=
  globalPairing A localization leftKummer rightKummer localInvariant

@[simp]
theorem pairing_apply
    (localization : K →+* F)
    (leftKummer : KummerClass 59 F →+
      H1 (KummerTateCup.trivialLine (k := ZMod 59) (G := G)))
    (rightKummer : KummerClass 59 F →+ H1 A)
    (localInvariant : H2 A →ₗ[ZMod 59] ZMod 59)
    (x y : KummerClass 59 K) :
    pairing A localization leftKummer rightKummer localInvariant x y =
      localInvariant
        (KummerTateCup.orientedCupH1Classes A
          (leftKummer (LocalKummerTransport.map 59 localization x))
          (rightKummer (LocalKummerTransport.map 59 localization y))) :=
  rfl

/-! ## Genuine discrete Kummer specialization -/

/-- Pull the canonical discrete Kummer--Tate pairing over `F` back to the
global Kummer quotient over `K`.

The primitive root constructs the left orientation, and both Kummer maps are
the genuine maps from `LocalKummerH1`.  Thus the sole deep local input at this
boundary is the linear invariant on `H²`; no Kummer map or pairing value is
supplied independently. -/
def discretePairing
    (localization : K →+* F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (localInvariant :
      H2 (LocalKummerH1.rootsRepresentation 59 F) →ₗ[ZMod 59] ZMod 59) :
    WildKummerPairing.Pairing 59 K :=
  LocalKummerTransport.Pairing.pullback localization
    (DiscreteKummerTatePairing.localPairing F zeta hzeta localInvariant)

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Quotient-level readback of the genuine discrete specialization. -/
@[simp]
theorem discretePairing_apply
    (localization : K →+* F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (localInvariant :
      H2 (LocalKummerH1.rootsRepresentation 59 F) →ₗ[ZMod 59] ZMod 59)
    (x y : KummerClass 59 K) :
    discretePairing localization zeta hzeta localInvariant x y =
      localInvariant
        (KummerTateCup.orientedCupH1Classes
          (LocalKummerH1.rootsRepresentation 59 F)
          (KummerOrientation.leftKummerMap 59 F zeta hzeta
            (LocalKummerTransport.map 59 localization x))
          (LocalKummerH1.map 59 F
            (LocalKummerTransport.map 59 localization y))) :=
  rfl

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Representative readback after localization, with both actual Kummer
classes exposed.  This is the concrete target for an independent comparison
with the old 59-reading. -/
@[simp]
theorem discretePairing_classOfUnit
    (localization : K →+* F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (localInvariant :
      H2 (LocalKummerH1.rootsRepresentation 59 F) →ₗ[ZMod 59] ZMod 59)
    (a b : Kˣ) :
    discretePairing localization zeta hzeta localInvariant
        (WildKummerPairing.classOfUnit 59 K (Additive.ofMul a))
        (WildKummerPairing.classOfUnit 59 K (Additive.ofMul b)) =
      localInvariant
        (KummerTateCup.orientedCupH1Classes
          (LocalKummerH1.rootsRepresentation 59 F)
          (KummerOrientation.orientH1 59 F zeta hzeta
            (LocalKummerH1.classOfUnit 59 F
              (LocalKummerTransport.unitMap localization a)))
          (LocalKummerH1.classOfUnit 59 F
            (LocalKummerTransport.unitMap localization b))) :=
  rfl

/-! ## Actual completion at the selected place -/

/-- The remaining readout type after fixing the actual adic completion.

This is deliberately named a *discrete* readout.  It acts on the ordinary
group cohomology currently constructed in this repository; it is not yet a
claim that Mathlib's canonical continuous local invariant has been built or
identified with this map.  That comparison remains a later theorem. -/
abbrev CompletionDiscreteH2Readout59
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  H2 (LocalKummerH1.rootsRepresentation 59
      (LocalField59 K distinguishedPlace)) →ₗ[ZMod 59] ZMod 59

/-- The quotient pairing on `K` obtained from its actual completion at
`distinguishedPlace`.

The local field and localization embedding are canonical constructions, and
the primitive root is the cyclotomic extension's fixed noncomputable choice.
The supplied map is only the interim discrete `H²` readout;
no continuous-local-invariant identification is asserted here. -/
def actualCompletionPairing
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (discreteReadout : CompletionDiscreteH2Readout59 distinguishedPlace) :
    WildKummerPairing.Pairing 59 K :=
  discretePairing
    (localization59 K distinguishedPlace)
    (localPrimitiveRoot59 K distinguishedPlace)
    (localPrimitiveRoot59_isPrimitive K distinguishedPlace)
    discreteReadout

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Quotient-level cup/readout formula at the actual completion. -/
@[simp]
theorem actualCompletionPairing_apply
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (discreteReadout : CompletionDiscreteH2Readout59 distinguishedPlace)
    (x y : KummerClass 59 K) :
    actualCompletionPairing distinguishedPlace discreteReadout x y =
      discreteReadout
        (KummerTateCup.orientedCupH1Classes
          (LocalKummerH1.rootsRepresentation 59
            (LocalField59 K distinguishedPlace))
          (KummerOrientation.leftKummerMap 59
            (LocalField59 K distinguishedPlace)
            (localPrimitiveRoot59 K distinguishedPlace)
            (localPrimitiveRoot59_isPrimitive K distinguishedPlace)
            (LocalKummerTransport.map 59
              (localization59 K distinguishedPlace) x))
          (LocalKummerH1.map 59 (LocalField59 K distinguishedPlace)
            (LocalKummerTransport.map 59
              (localization59 K distinguishedPlace) y))) :=
  rfl

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Representative readback at the actual completion, exposing the two
localized Kummer classes consumed by the discrete cup product. -/
@[simp]
theorem actualCompletionPairing_classOfUnit
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (discreteReadout : CompletionDiscreteH2Readout59 distinguishedPlace)
    (a b : Kˣ) :
    actualCompletionPairing distinguishedPlace discreteReadout
        (WildKummerPairing.classOfUnit 59 K (Additive.ofMul a))
        (WildKummerPairing.classOfUnit 59 K (Additive.ofMul b)) =
      discreteReadout
        (KummerTateCup.orientedCupH1Classes
          (LocalKummerH1.rootsRepresentation 59
            (LocalField59 K distinguishedPlace))
          (KummerOrientation.orientH1 59
            (LocalField59 K distinguishedPlace)
            (localPrimitiveRoot59 K distinguishedPlace)
            (localPrimitiveRoot59_isPrimitive K distinguishedPlace)
            (LocalKummerH1.classOfUnit 59
              (LocalField59 K distinguishedPlace)
              (LocalKummerTransport.unitMap
                (localization59 K distinguishedPlace) a)))
          (LocalKummerH1.classOfUnit 59
            (LocalField59 K distinguishedPlace)
            (LocalKummerTransport.unitMap
              (localization59 K distinguishedPlace) b))) :=
  rfl

/-- Install the cohomological quotient pairing in the real 59-local core.

The final argument is deliberately an independent theorem: it compares the
canonical cohomological reading with the pre-existing old wild reading on
the strict carriers, but never defines either reading from the other. -/
def toReflectedWildKummerCoreAt59
    (localization : K →+* F)
    (leftKummer : KummerClass 59 F →+
      H1 (KummerTateCup.trivialLine (k := ZMod 59) (G := G)))
    (rightKummer : KummerClass 59 F →+ H1 A)
    (localInvariant : H2 A →ₗ[ZMod 59] ZMod 59)
    (landing : ReflectedEmptySupportLanding827 rho rhoQ omega chi)
    (hcalibration : ∀ x : OldPrimal59 rho chi,
      ∀ y : OldReflectedDual59 rho omega chi,
        pairing A localization leftKummer rightKummer localInvariant
            (toKummerClass x) (toKummerClass y) =
          wild.reading x y) :
    ReflectedWildKummerCoreAt59 rho rhoQ omega chi
      distinguishedPlace wild where
  pairing := pairing A localization leftKummer rightKummer localInvariant
  landing := landing
  old_calibration := hcalibration

@[simp]
theorem toReflectedWildKummerCoreAt59_pairing_apply
    (localization : K →+* F)
    (leftKummer : KummerClass 59 F →+
      H1 (KummerTateCup.trivialLine (k := ZMod 59) (G := G)))
    (rightKummer : KummerClass 59 F →+ H1 A)
    (localInvariant : H2 A →ₗ[ZMod 59] ZMod 59)
    (landing : ReflectedEmptySupportLanding827 rho rhoQ omega chi)
    (hcalibration : ∀ x : OldPrimal59 rho chi,
      ∀ y : OldReflectedDual59 rho omega chi,
        pairing A localization leftKummer rightKummer localInvariant
            (toKummerClass x) (toKummerClass y) =
          wild.reading x y)
    (x y : KummerClass 59 K) :
    (toReflectedWildKummerCoreAt59 A rho rhoQ omega chi distinguishedPlace
      wild localization leftKummer rightKummer localInvariant landing
      hcalibration).pairing x y =
        pairing A localization leftKummer rightKummer localInvariant x y :=
  rfl

/-! ## Canonical-action specialization -/

/-- With the actual cyclotomic actions, the strict-to-827-supported landing
is no longer an input.  The cohomological arithmetic data and its independent
old-reading calibration directly construct the real quotient-first core. -/
def toCanonicalReflectedWildKummerCoreAt59
    (localization : K →+* F)
    (leftKummer : KummerClass 59 F →+
      H1 (KummerTateCup.trivialLine (k := ZMod 59) (G := G)))
    (rightKummer : KummerClass 59 F →+ H1 A)
    (localInvariant : H2 A →ₗ[ZMod 59] ZMod 59)
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (wild : OldWildInterface59
      (cyclotomicStrictSelmerRepresentation59 K) omega chi
      distinguishedPlace)
    (hcalibration :
      ∀ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi,
      ∀ y : OldReflectedDual59
        (cyclotomicStrictSelmerRepresentation59 K) omega chi,
        pairing A localization leftKummer rightKummer localInvariant
            (toKummerClass x) (toKummerClass y) =
          wild.reading x y) :
    ReflectedWildKummerCoreAt59
      (cyclotomicStrictSelmerRepresentation59 K)
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi distinguishedPlace wild :=
  toReflectedWildKummerCoreAt59 A
    (cyclotomicStrictSelmerRepresentation59 K)
    (cyclotomicQRelaxedSelmerRepresentation827 K)
    omega chi distinguishedPlace wild localization leftKummer rightKummer
    localInvariant
    (cyclotomicReflectedEmptySupportLanding827 K omega chi)
    hcalibration

/-- Canonical-action 59-core built from the genuine discrete Kummer maps.

Landing is derived from the common ambient cyclotomic action.  Apart from the
structural localization map and the already-existing old interface, the
visible arithmetic inputs are exactly a primitive root, an honest `H²`
invariant, and an independent theorem calibrating the resulting pairing
against the old reading. -/
def toCanonicalDiscreteReflectedWildKummerCoreAt59
    (localization : K →+* F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (localInvariant :
      H2 (LocalKummerH1.rootsRepresentation 59 F) →ₗ[ZMod 59] ZMod 59)
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (wild : OldWildInterface59
      (cyclotomicStrictSelmerRepresentation59 K) omega chi
      distinguishedPlace)
    (hcalibration :
      ∀ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi,
      ∀ y : OldReflectedDual59
        (cyclotomicStrictSelmerRepresentation59 K) omega chi,
        discretePairing localization zeta hzeta localInvariant
            (toKummerClass x) (toKummerClass y) =
          wild.reading x y) :
    ReflectedWildKummerCoreAt59
      (cyclotomicStrictSelmerRepresentation59 K)
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi distinguishedPlace wild where
  pairing := discretePairing localization zeta hzeta localInvariant
  landing := cyclotomicReflectedEmptySupportLanding827 K omega chi
  old_calibration := hcalibration

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem toCanonicalDiscreteReflectedWildKummerCoreAt59_pairing_apply
    (localization : K →+* F)
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)
    (localInvariant :
      H2 (LocalKummerH1.rootsRepresentation 59 F) →ₗ[ZMod 59] ZMod 59)
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (wild : OldWildInterface59
      (cyclotomicStrictSelmerRepresentation59 K) omega chi
      distinguishedPlace)
    (hcalibration :
      ∀ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi,
      ∀ y : OldReflectedDual59
        (cyclotomicStrictSelmerRepresentation59 K) omega chi,
        discretePairing localization zeta hzeta localInvariant
            (toKummerClass x) (toKummerClass y) =
          wild.reading x y)
    (x y : KummerClass 59 K) :
    (toCanonicalDiscreteReflectedWildKummerCoreAt59
      localization zeta hzeta localInvariant omega chi distinguishedPlace
      wild hcalibration).pairing x y =
        discretePairing localization zeta hzeta localInvariant x y :=
  rfl

/-- The canonical-action core at the actual selected completion.

At this boundary the completion, localization, primitive root, Kummer maps,
and strict-to-relaxed landing are all derived.  The only new arithmetic inputs
are the interim discrete `H²` readout and an independent calibration theorem
against the old reading.  Identifying the discrete readout with the canonical
continuous local invariant remains an explicit future comparison theorem. -/
def toActualCompletionCanonicalReflectedWildKummerCoreAt59
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (discreteReadout : CompletionDiscreteH2Readout59 distinguishedPlace)
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (wild : OldWildInterface59
      (cyclotomicStrictSelmerRepresentation59 K) omega chi
      distinguishedPlace)
    (hcalibration :
      ∀ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi,
      ∀ y : OldReflectedDual59
        (cyclotomicStrictSelmerRepresentation59 K) omega chi,
        actualCompletionPairing distinguishedPlace discreteReadout
            (toKummerClass x) (toKummerClass y) =
          wild.reading x y) :
    ReflectedWildKummerCoreAt59
      (cyclotomicStrictSelmerRepresentation59 K)
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi distinguishedPlace wild :=
  toCanonicalDiscreteReflectedWildKummerCoreAt59
    (localization59 K distinguishedPlace)
    (localPrimitiveRoot59 K distinguishedPlace)
    (localPrimitiveRoot59_isPrimitive K distinguishedPlace)
    discreteReadout omega chi distinguishedPlace wild hcalibration

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem toActualCompletionCanonicalReflectedWildKummerCoreAt59_pairing_apply
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (discreteReadout : CompletionDiscreteH2Readout59 distinguishedPlace)
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (wild : OldWildInterface59
      (cyclotomicStrictSelmerRepresentation59 K) omega chi
      distinguishedPlace)
    (hcalibration :
      ∀ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi,
      ∀ y : OldReflectedDual59
        (cyclotomicStrictSelmerRepresentation59 K) omega chi,
        actualCompletionPairing distinguishedPlace discreteReadout
            (toKummerClass x) (toKummerClass y) =
          wild.reading x y)
    (x y : KummerClass 59 K) :
    (toActualCompletionCanonicalReflectedWildKummerCoreAt59
      distinguishedPlace discreteReadout omega chi wild hcalibration).pairing
        x y =
      actualCompletionPairing distinguishedPlace discreteReadout x y :=
  rfl

end Fermat.FiftyNine.Conservation.KummerTateLocalization59
