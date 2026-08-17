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
import Fermat.Conservation.CohomologicalKummerPairing
import Fermat.FiftyNine.Conservation.VostokovLocalization59

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.KummerTateLocalization59

open groupCohomology
open Fermat.Conservation
open Fermat.Conservation.CohomologicalKummerPairing
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TameSymbol
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827
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
      (Additive G →+ ZMod 59))
    (rightKummer : KummerClass 59 F →+ H1 A)
    (localInvariant : H2 A →ₗ[ZMod 59] ZMod 59) :
    WildKummerPairing.Pairing 59 K :=
  globalPairing A localization leftKummer rightKummer localInvariant

@[simp]
theorem pairing_apply
    (localization : K →+* F)
    (leftKummer : KummerClass 59 F →+
      (Additive G →+ ZMod 59))
    (rightKummer : KummerClass 59 F →+ H1 A)
    (localInvariant : H2 A →ₗ[ZMod 59] ZMod 59)
    (x y : KummerClass 59 K) :
    pairing A localization leftKummer rightKummer localInvariant x y =
      localInvariant
        (KummerTateCup.orientedCupH1 A
          (leftKummer (LocalKummerTransport.map 59 localization x))
          (rightKummer (LocalKummerTransport.map 59 localization y))) :=
  rfl

/-- Install the cohomological quotient pairing in the real 59-local core.

The final argument is deliberately an independent theorem: it compares the
canonical cohomological reading with the pre-existing old wild reading on
the strict carriers, but never defines either reading from the other. -/
def toReflectedWildKummerCoreAt59
    (localization : K →+* F)
    (leftKummer : KummerClass 59 F →+
      (Additive G →+ ZMod 59))
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
      (Additive G →+ ZMod 59))
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

end Fermat.FiftyNine.Conservation.KummerTateLocalization59
