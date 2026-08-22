/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The two literal Kummer-class shapes entering V3 at conductor 59

This is the C1 shape audit for the strict wild-localization core.  The two
inputs are not the normalized Fermat factors: they are exactly the Kummer
classes of an old primal Selmer element and a q-relaxed reflected Selmer
element.  Their field representatives are the quotient representatives
chosen by `SelmerEigenspace`, with explicit readback to those same classes.

At the current Artin--Hasse boundary there is no theorem seating either
literal input in the advertised generator subgroup.  Accordingly the
canonical campaign decomposition below is deliberately `residualOnly`: its
covered factors are zero and its residuals are the complete input classes.
This is an evidence audit, not a claim of subgroup nonmembership.

The final theorem records a second structural fact about the reflected
shape.  A normalized q-relaxed fiber point has 827-coordinate one, whereas
every point in the canonical strict inclusion has coordinate zero.  Hence a
normalized point cannot secretly be an old strict point.  No complement,
section, or splitting is constructed.
-/
import Fermat.Exponents.FiftyNine.Conservation.VostokovLocalization59

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.VostokovShapeAudit59

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TamePlacePairing
open Fermat.FiftyNine.Conservation.ArtinHasseInventory
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827
open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.PointedTateIncidence
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.UlamReadout827
open Fermat.FiftyNine.Conservation.VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  (rho : SelmerDeltaRepresentation (R := 𝓞 K) (K := K) (p := 59)
    (Delta := GaloisIndex59))
  (rhoQ : QRelaxedSelmerDeltaRepresentation827 K GaloisIndex59)
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

/-! ## Literal V3 inputs and their representatives -/

/-- The left input to the V3 pairing is exactly the seated old-primal
Kummer class. -/
abbrev statewiseKummerClass (x : OldPrimal59 rho chi) :
    TameSymbol.KummerClass 59 K :=
  toKummerClass x

/-- The right input to the V3 pairing is exactly the seated q-relaxed
reflected Kummer class. -/
abbrev transverseKummerClass
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    TameSymbol.KummerClass 59 K :=
  toKummerClassAt y

/-- The chosen field representative of the literal statewise input. -/
abbrev statewiseRepresentative (x : OldPrimal59 rho chi) : Kˣ :=
  quotientRepresentative x

/-- The chosen field representative of the literal transverse input. -/
abbrev transverseRepresentative
    (y : QRelaxedReflectedDual827 rhoQ omega chi) : Kˣ :=
  quotientRepresentativeAt y

omit [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The statewise representative maps back to the exact Kummer class used
by V3. -/
theorem statewiseRepresentative_readback (x : OldPrimal59 rho chi) :
    Additive.ofMul
        ((statewiseRepresentative rho chi x : Kˣ) :
          Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) =
      statewiseKummerClass rho chi x := by
  change Additive.ofMul
      ((quotientRepresentative x : Kˣ) :
        Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) =
    Additive.ofMul (toKummerQuotient x)
  exact congrArg Additive.ofMul (quotientRepresentative_mk x)

omit [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The supported representative maps back to the exact transverse Kummer
class used by V3. -/
theorem transverseRepresentative_readback
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    Additive.ofMul
        ((transverseRepresentative rhoQ omega chi y : Kˣ) :
          Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) =
      transverseKummerClass rhoQ omega chi y := by
  change Additive.ofMul
      ((quotientRepresentativeAt y : Kˣ) :
        Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) =
    Additive.ofMul (toKummerQuotientAt y)
  exact congrArg Additive.ofMul (quotientRepresentativeAt_mk y)

/-! ## Honest position at the current Artin--Hasse boundary -/

variable {zeta : K} (hZeta : IsPrimitiveRoot zeta 59)
  (solution : PrimitiveSecondCaseSolution)
  (hz : (59 : ℤ) ∣ solution.z)

/-- The canonical C1 decomposition of the two literal V3 classes.  The
normalized-factor evidence is retained, but neither literal pairing input is
silently identified with a normalized factor or an advertised generator. -/
def inputResidualOnly
    (normalized : NormalizedStateFactorArtinHasseDecomposition
      hZeta solution hz)
    (x : OldPrimal59 rho chi)
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    CampaignArtinHasseFactorDecomposition hZeta solution hz
      (statewiseKummerClass rho chi x)
      (transverseKummerClass rhoQ omega chi y) :=
  CampaignArtinHasseFactorDecomposition.residualOnly normalized
    (statewiseKummerClass rho chi x)
    (transverseKummerClass rhoQ omega chi y)

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem inputResidualOnly_statewise_covered
    (normalized : NormalizedStateFactorArtinHasseDecomposition
      hZeta solution hz)
    (x : OldPrimal59 rho chi)
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    (inputResidualOnly rho rhoQ omega chi hZeta solution hz
      normalized x y).statewiseSelmerLift.covered = 0 :=
  rfl

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem inputResidualOnly_statewise_residual
    (normalized : NormalizedStateFactorArtinHasseDecomposition
      hZeta solution hz)
    (x : OldPrimal59 rho chi)
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    (inputResidualOnly rho rhoQ omega chi hZeta solution hz
      normalized x y).statewiseSelmerLift.residual =
        statewiseKummerClass rho chi x :=
  rfl

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem inputResidualOnly_transverse_covered
    (normalized : NormalizedStateFactorArtinHasseDecomposition
      hZeta solution hz)
    (x : OldPrimal59 rho chi)
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    (inputResidualOnly rho rhoQ omega chi hZeta solution hz
      normalized x y).transverseDetectorComponent.covered = 0 :=
  rfl

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
@[simp]
theorem inputResidualOnly_transverse_residual
    (normalized : NormalizedStateFactorArtinHasseDecomposition
      hZeta solution hz)
    (x : OldPrimal59 rho chi)
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    (inputResidualOnly rho rhoQ omega chi hZeta solution hz
      normalized x y).transverseDetectorComponent.residual =
        transverseKummerClass rhoQ omega chi y :=
  rfl

/-! ## Direct connection to the V3 core -/

variable
  {distinguishedPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
  {wild : OldWildInterface59 rho omega chi distinguishedPlace}

omit [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Evaluation of the V3 reading exposes exactly the two audited classes;
no normalized-factor substitution occurs between the carrier and the
quotient pairing. -/
theorem readingAt59_exact_inputs
    (core : ReflectedWildKummerCoreAt59 rho rhoQ omega chi
      distinguishedPlace wild)
    (x : OldPrimal59 rho chi)
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    core.readingAt59 x y =
      core.pairing
        (statewiseKummerClass rho chi x)
        (transverseKummerClass rhoQ omega chi y) :=
  rfl

/-! ## The normalized reflected shape genuinely leaves the strict range -/

variable (selectedPlace : Place827 K)

omit [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- Every canonically included strict reflected class has zero selected
827-coordinate. -/
theorem qLocalizationCoordinate827_oldReflected_eq_zero
    (landing : ReflectedEmptySupportLanding827 rho rhoQ omega chi)
    (y : OldReflectedDual59 rho omega chi) :
    qLocalizationCoordinate827 rhoQ omega chi selectedPlace
        (oldReflectedToQRelaxed827 rho rhoQ omega chi landing y) = 0 := by
  have hzero := supportValuation_emptySupportInclusion_eq_zero
    (R := 𝓞 K) (K := K) (p := 59) (S := placesOver827 K) y.1
  have hselected := congrFun hzero selectedPlace
  exact hselected

/-- A normalized q-relaxed fiber point is not in the range of the canonical
strict inclusion: its selected coordinate is one, while that range has
selected coordinate zero. -/
theorem normalizedFiber_not_mem_range_oldReflected
    (landing : ReflectedEmptySupportLanding827 rho rhoQ omega chi)
    (y : NormalizedReflectedFiber827 rhoQ omega chi selectedPlace) :
    y.1 ∉ Set.range
      (oldReflectedToQRelaxed827 rho rhoQ omega chi landing) := by
  rintro ⟨old, hold⟩
  have hnormalized :
      qLocalizationCoordinate827 rhoQ omega chi selectedPlace y.1 = 1 := by
    rw [← reflectedBoundaryFunctional827_eq_qLocalizationCoordinate827]
    exact y.2
  have hzero :
      qLocalizationCoordinate827 rhoQ omega chi selectedPlace y.1 = 0 := by
    rw [← hold]
    exact qLocalizationCoordinate827_oldReflected_eq_zero
      rho rhoQ omega chi selectedPlace landing old
  exact one_ne_zero (hnormalized.symm.trans hzero)

end Fermat.FiftyNine.Conservation.VostokovShapeAudit59
