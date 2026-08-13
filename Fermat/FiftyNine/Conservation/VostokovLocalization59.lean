/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Reduce the 59-local Ulam producer to a wild Kummer pairing core

This module proves the requested constructor reduction.  Its arithmetic
input is a representative-level Kummer pairing, the minimal receipt that the
canonical empty-support inclusion lands in the q-relaxed reflected
eigenspace, and calibration against the existing old wild reading.

The quotient-level symbol is derived by canonical descent.  Its full
integral group-algebra adjoint law is formal on the two fixed character
eigenspaces, so no extra adjoint field is retained.  The representative
pairing is the strictly smaller named arithmetic frontier: this file does not
construct a 59-adic completion/localization map or identify the input with a
Vostokov residue formula or Hilbert symbol.  It makes no Steinberg,
norm-residue, or reciprocity claim.
-/
import Fermat.Conservation.WildKummerPairing
import Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827
import Fermat.FiftyNine.Conservation.UlamReadout827
import Fermat.FiftyNine.Conservation.ArtinHasseInventory

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.VostokovLocalization59

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TamePlacePairing
open Fermat.Conservation.WildKummerPairing
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.ArtinHasseInventory
open Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827
open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  (rho : SelmerDeltaRepresentation (R := 𝓞 K) (K := K) (p := 59)
    (Delta := GaloisIndex59))
  (rhoQ : QRelaxedSelmerDeltaRepresentation827 K GaloisIndex59)
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

/-- The concrete old primal carrier used by the 59-local assembly. -/
abbrev OldPrimal59 := SelmerChi rho chi

/-- The concrete old reflected carrier used by the 59-local assembly. -/
abbrev OldReflectedDual59 := DOmegaSelmerChiStar rho omega chi

/-- The distinguished wild-place interface on the two concrete old seated
eigenspaces. -/
abbrev OldWildInterface59
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  WildLocalInterface 59 GaloisIndex59 omega chi
    (IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (OldPrimal59 rho chi) (OldReflectedDual59 rho omega chi)
    distinguishedPlace

/-- **STRICT WILD-LOCALIZATION ARITHMETIC CORE.**

Only a representative pairing is stored; its total Kummer pairing and
descent receipt are constructed by `WildKummerPairing.Core.ofRepresentative`.
The adjoint law is not a field: it follows formally from the `chi` and
`omega * chi⁻¹` eigenlaws.  Producing this pairing from completed 59-adic
Laurent-series calculus remains the named arithmetic task. -/
structure ReflectedWildKummerCoreAt59
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (wild : OldWildInterface59 rho omega chi distinguishedPlace) where
  representative : WildKummerPairing.RepresentativePairing 59 K
  landing : ReflectedEmptySupportLanding827 rho rhoQ omega chi
  old_calibration : ∀ x : OldPrimal59 rho chi,
      ∀ y : OldReflectedDual59 rho omega chi,
    representative.descend (toKummerClass x) (toKummerClass y) =
      wild.reading x y

namespace ReflectedWildKummerCoreAt59

variable {rho rhoQ omega chi}
  {distinguishedPlace : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
  {wild : OldWildInterface59 rho omega chi distinguishedPlace}

/-- The total wild Kummer core canonically descended from the stored
representative formula. -/
def wildKummerCore
    (core : ReflectedWildKummerCoreAt59 rho rhoQ omega chi
      distinguishedPlace wild) :
    WildKummerPairing.Core 59 K :=
  WildKummerPairing.Core.ofRepresentative core.representative

/-- The q-relaxed reading obtained by evaluating the descended Kummer symbol
on the literal seated Kummer-class maps. -/
def readingAt59
    (core : ReflectedWildKummerCoreAt59 rho rhoQ omega chi
      distinguishedPlace wild) :
    OldPrimal59 rho chi →+
      (QRelaxedReflectedDual827 rhoQ omega chi →+ ZMod 59) :=
  AddMonoidHom.compl₂
    (core.wildKummerCore.pairing.comp
      (toKummerClass (rho := rho) (chi := chi)))
    (toKummerClassAt (rho := rhoQ)
      (eta := InvolutiveBase.reflectedCharacter omega chi))

@[simp]
theorem readingAt59_apply
    (core : ReflectedWildKummerCoreAt59 rho rhoQ omega chi
      distinguishedPlace wild)
    (x : OldPrimal59 rho chi)
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    core.readingAt59 x y =
      core.representative.descend (toKummerClass x) (toKummerClassAt y) :=
  rfl

/-! ### The formal character adjoint law -/

/-- A single group-algebra term acts on the primal eigenspace by its
character scalar. -/
private theorem single_smul_oldPrimal
    (delta : GaloisIndex59) (c : PadicInt 59)
    (x : OldPrimal59 rho chi) :
    MonoidAlgebra.single delta c • x =
      (c * (chi delta : PadicInt 59)) • x := by
  have hdelta :
      characterEigenspaceRepresentation rho chi delta x =
        (chi delta : PadicInt 59) • x := by
    apply Subtype.ext
    exact (mem_characterEigenspace_iff rho chi x.1).mp x.property delta
  calc
    MonoidAlgebra.single delta c • x =
        c • characterEigenspaceRepresentation rho chi delta x := by
      change ((characterEigenspaceRepresentation rho chi).asAlgebraHom
        (MonoidAlgebra.single delta c)) x = _
      rw [Representation.asAlgebraHom_single]
      rfl
    _ = c • ((chi delta : PadicInt 59) • x) := by rw [hdelta]
    _ = (c * (chi delta : PadicInt 59)) • x := by rw [smul_smul]

/-- Hashing a single term and acting on the reflected eigenspace produces
the same primal-character scalar. -/
private theorem hash_single_smul_qRelaxedReflected
    (delta : GaloisIndex59) (c : PadicInt 59)
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    InvolutiveBase.hash omega (MonoidAlgebra.single delta c) • y =
      (c * (chi delta : PadicInt 59)) • y := by
  rw [InvolutiveBase.hash_apply_single]
  have hdelta : (characterEigenspaceRepresentationAt rhoQ
      (InvolutiveBase.reflectedCharacter omega chi)) delta⁻¹ y =
      (InvolutiveBase.reflectedCharacter omega chi delta⁻¹ :
        PadicInt 59) • y := by
    apply Subtype.ext
    exact (mem_characterEigenspaceAt_iff rhoQ
      (InvolutiveBase.reflectedCharacter omega chi) y.1).mp
        y.property delta⁻¹
  calc
    MonoidAlgebra.single delta⁻¹ (c * (omega delta : PadicInt 59)) • y =
        (c * (omega delta : PadicInt 59)) •
          (characterEigenspaceRepresentationAt rhoQ
            (InvolutiveBase.reflectedCharacter omega chi)) delta⁻¹ y := by
      change ((characterEigenspaceRepresentationAt rhoQ
        (InvolutiveBase.reflectedCharacter omega chi)).asAlgebraHom
        (MonoidAlgebra.single delta⁻¹
          (c * (omega delta : PadicInt 59)))) y = _
      rw [Representation.asAlgebraHom_single]
      rfl
    _ = (c * (omega delta : PadicInt 59)) •
          ((InvolutiveBase.reflectedCharacter omega chi delta⁻¹ :
            PadicInt 59) • y) := by rw [hdelta]
    _ = ((c * (omega delta : PadicInt 59)) *
          (InvolutiveBase.reflectedCharacter omega chi delta⁻¹ :
            PadicInt 59)) • y := by rw [smul_smul]
    _ = (c * (chi delta : PadicInt 59)) • y := by
      congr 1
      simp [InvolutiveBase.reflectedCharacter, mul_assoc, mul_comm,
        mul_left_comm]

/-- The generator adjoint law is forced by the two eigenspace predicates and
additivity of the Kummer symbol.  It is therefore a theorem, not arithmetic
input. -/
private theorem single_adjoint_law
    (core : ReflectedWildKummerCoreAt59 rho rhoQ omega chi
      distinguishedPlace wild)
    (delta : GaloisIndex59) (c : PadicInt 59)
    (x : OldPrimal59 rho chi)
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    core.readingAt59 (MonoidAlgebra.single delta c • x) y =
      core.readingAt59 x
        (InvolutiveBase.hash omega (MonoidAlgebra.single delta c) • y) := by
  rw [single_smul_oldPrimal, hash_single_smul_qRelaxedReflected]
  change core.representative.descend
      (toKummerClass ((c * (chi delta : PadicInt 59)) • x))
      (toKummerClassAt y) =
    core.representative.descend (toKummerClass x)
      (toKummerClassAt ((c * (chi delta : PadicInt 59)) • y))
  change core.representative.descend
      ((PadicInt.toZMod (c * (chi delta : PadicInt 59))).val •
        toKummerClass x)
      (toKummerClassAt y) =
    core.representative.descend (toKummerClass x)
      ((PadicInt.toZMod (c * (chi delta : PadicInt 59))).val •
        toKummerClassAt y)
  rw [map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply]

/-- The full `hash omega` adjoint law, extended from single terms by linear
induction on the integral group algebra. -/
theorem adjoint_law
    (core : ReflectedWildKummerCoreAt59 rho rhoQ omega chi
      distinguishedPlace wild)
    (a : IntegralPadicGroupAlgebra 59 GaloisIndex59)
    (x : OldPrimal59 rho chi)
    (y : QRelaxedReflectedDual827 rhoQ omega chi) :
    core.readingAt59 (a • x) y =
      core.readingAt59 x ((InvolutiveBase.hash omega a) • y) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero =>
      simpa only [zero_smul, map_zero, AddMonoidHom.zero_apply]
  | add a b ha hb =>
      calc
        core.readingAt59 ((a + b) • x) y =
            core.readingAt59 (a • x + b • x) y := by rw [add_smul]
        _ = core.readingAt59 (a • x) y +
            core.readingAt59 (b • x) y := by
          rw [map_add, AddMonoidHom.add_apply]
        _ = core.readingAt59 x ((InvolutiveBase.hash omega a) • y) +
            core.readingAt59 x ((InvolutiveBase.hash omega b) • y) := by
          rw [ha, hb]
        _ = core.readingAt59 x
            ((InvolutiveBase.hash omega a) • y +
              (InvolutiveBase.hash omega b) • y) := by rw [map_add]
        _ = core.readingAt59 x
            (((InvolutiveBase.hash omega a) +
              (InvolutiveBase.hash omega b)) • y) := by rw [add_smul]
        _ = core.readingAt59 x
            ((InvolutiveBase.hash omega (a + b)) • y) := by
          exact congrArg
            (fun z : IntegralPadicGroupAlgebra 59 GaloisIndex59 ↦
              core.readingAt59 x (z • y))
            (map_add (InvolutiveBase.hash omega) a b).symm
  | single delta c =>
      exact core.single_adjoint_law delta c x y

/-! ### V1 factorization feeds the total symbol -/

/-- Expanding the left input by explicit Artin--Hasse coefficients reduces
its symbol to the banked zeta, denominator, and generated-unit classes.  No
value of those symbols is asserted here. -/
theorem pairing_artinHasseExpansion_left
    (core : ReflectedWildKummerCoreAt59 rho rhoQ omega chi
      distinguishedPlace wild)
    {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
    {left : TameSymbol.KummerClass 59 K}
    (d : ArtinHasseKummerDecomposition hZeta left)
    (right : TameSymbol.KummerClass 59 K) :
    core.wildKummerCore.pairing left right =
      d.zetaCoefficient •
          core.wildKummerCore.pairing (zetaKummerClass hZeta) right +
        d.denominatorCoefficient •
          core.wildKummerCore.pairing
            (fixedDenominatorKummerClass hZeta) right +
        ∑ i, d.generatedCoefficient i •
          core.wildKummerCore.pairing (generatedUnitKummerClass hZeta i) right := by
  let pairingRight : TameSymbol.KummerClass 59 K →+ ZMod 59 :=
    (AddMonoidHom.eval right).comp core.wildKummerCore.pairing
  change pairingRight left =
    d.zetaCoefficient • pairingRight (zetaKummerClass hZeta) +
      d.denominatorCoefficient •
        pairingRight (fixedDenominatorKummerClass hZeta) +
      ∑ i, d.generatedCoefficient i •
        pairingRight (generatedUnitKummerClass hZeta i)
  have pairingRight_zsmul (n : ℤ)
      (x : TameSymbol.KummerClass 59 K) :
      pairingRight (n • x) = n • pairingRight x :=
    pairingRight.map_zsmul n x
  calc
    pairingRight left =
        pairingRight
          (d.zetaCoefficient • zetaKummerClass hZeta +
            d.denominatorCoefficient • fixedDenominatorKummerClass hZeta +
            ∑ i, d.generatedCoefficient i • generatedUnitKummerClass hZeta i) :=
      congrArg pairingRight d.decomposition
    _ = _ := by
      simp only [map_add, map_sum]
      simp_rw [pairingRight_zsmul]

/-- The analogous explicit coefficient expansion in the right input. -/
theorem pairing_artinHasseExpansion_right
    (core : ReflectedWildKummerCoreAt59 rho rhoQ omega chi
      distinguishedPlace wild)
    {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
    (left : TameSymbol.KummerClass 59 K)
    {right : TameSymbol.KummerClass 59 K}
    (d : ArtinHasseKummerDecomposition hZeta right) :
    core.wildKummerCore.pairing left right =
      d.zetaCoefficient •
          core.wildKummerCore.pairing left (zetaKummerClass hZeta) +
        d.denominatorCoefficient •
          core.wildKummerCore.pairing left
            (fixedDenominatorKummerClass hZeta) +
        ∑ i, d.generatedCoefficient i •
          core.wildKummerCore.pairing left (generatedUnitKummerClass hZeta i) := by
  let pairingLeft := core.wildKummerCore.pairing left
  change pairingLeft right =
    d.zetaCoefficient • pairingLeft (zetaKummerClass hZeta) +
      d.denominatorCoefficient •
        pairingLeft (fixedDenominatorKummerClass hZeta) +
      ∑ i, d.generatedCoefficient i •
        pairingLeft (generatedUnitKummerClass hZeta i)
  have pairingLeft_zsmul (n : ℤ)
      (x : TameSymbol.KummerClass 59 K) :
      pairingLeft (n • x) = n • pairingLeft x :=
    pairingLeft.map_zsmul n x
  calc
    pairingLeft right =
        pairingLeft
          (d.zetaCoefficient • zetaKummerClass hZeta +
            d.denominatorCoefficient • fixedDenominatorKummerClass hZeta +
            ∑ i, d.generatedCoefficient i • generatedUnitKummerClass hZeta i) :=
      congrArg pairingLeft d.decomposition
    _ = _ := by
      simp only [map_add, map_sum]
      simp_rw [pairingLeft_zsmul]

/-- A campaign factor decomposition expands the actual statewise/detector
symbol into the four covered/residual terms.  Thus V1's exact residual is
the literal input to the total V2 symbol, rather than a disconnected audit
label. -/
theorem pairing_campaignFactorDecomposition
    (core : ReflectedWildKummerCoreAt59 rho rhoQ omega chi
      distinguishedPlace wild)
    {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
    {solution : PrimitiveSecondCaseSolution}
    {hz : (59 : ℤ) ∣ solution.z}
    {statewiseClass detectorClass : TameSymbol.KummerClass 59 K}
    (d : CampaignArtinHasseFactorDecomposition hZeta solution hz
      statewiseClass detectorClass) :
    core.wildKummerCore.pairing statewiseClass detectorClass =
      (core.wildKummerCore.pairing
          d.statewiseSelmerLift.covered
          d.transverseDetectorComponent.covered +
        core.wildKummerCore.pairing
          d.statewiseSelmerLift.covered
          d.transverseDetectorComponent.residual) +
      (core.wildKummerCore.pairing
          d.statewiseSelmerLift.residual
          d.transverseDetectorComponent.covered +
        core.wildKummerCore.pairing
          d.statewiseSelmerLift.residual
          d.transverseDetectorComponent.residual) := by
  calc
    core.wildKummerCore.pairing statewiseClass detectorClass =
        core.wildKummerCore.pairing
          (d.statewiseSelmerLift.covered +
            d.statewiseSelmerLift.residual)
          detectorClass := congrArg
            (fun leftClass ↦ core.wildKummerCore.pairing leftClass detectorClass)
            d.statewiseSelmerLift.reconstruction
    _ = core.wildKummerCore.pairing
          (d.statewiseSelmerLift.covered +
            d.statewiseSelmerLift.residual)
          (d.transverseDetectorComponent.covered +
            d.transverseDetectorComponent.residual) := congrArg
              (core.wildKummerCore.pairing
                (d.statewiseSelmerLift.covered +
                  d.statewiseSelmerLift.residual))
              d.transverseDetectorComponent.reconstruction
    _ = _ := by
      simp only [map_add, AddMonoidHom.add_apply]
      ac_rfl

/-- Calibration against the old wild reading after the canonical strict to
q-relaxed inclusion. -/
theorem agrees_with_old
    (core : ReflectedWildKummerCoreAt59 rho rhoQ omega chi
      distinguishedPlace wild)
    (x : OldPrimal59 rho chi)
    (y : OldReflectedDual59 rho omega chi) :
    core.readingAt59 x
        (oldReflectedToQRelaxed827 rho rhoQ omega chi core.landing y) =
      wild.reading x y := by
  rw [readingAt59_apply,
    toKummerClassAt_oldReflectedToQRelaxed827]
  exact core.old_calibration x y

/-- **V3 LOCALIZATION CONSTRUCTOR.**  The representative pairing,
landing receipt, and old calibration inhabit Ulam's complete localization
producer. -/
def toReflectedWildLocalizationAt59
    (core : ReflectedWildKummerCoreAt59 rho rhoQ omega chi
      distinguishedPlace wild) :
    UlamReadout827.ReflectedWildLocalizationAt59
      (Place := IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (SelmerChi := OldPrimal59 rho chi)
      (DOmegaSelmerChiStar := OldReflectedDual59 rho omega chi)
      rhoQ omega chi distinguishedPlace wild where
  oldToQRelaxed := oldReflectedToQRelaxed827 rho rhoQ omega chi core.landing
  oldToQRelaxed_injective :=
    oldReflectedToQRelaxed827_injective rho rhoQ omega chi core.landing
  readingAt59 := core.readingAt59
  adjoint_law := core.adjoint_law
  agrees_with_old := core.agrees_with_old

/-- The constructor reduction in proposition form: an inhabitant of the
strict arithmetic core conditionally inhabits Ulam's complete localization
producer. -/
theorem nonempty_reflectedWildLocalizationAt59
    (core : ReflectedWildKummerCoreAt59 rho rhoQ omega chi
      distinguishedPlace wild) :
    Nonempty
      (UlamReadout827.ReflectedWildLocalizationAt59
        (Place := IsDedekindDomain.HeightOneSpectrum (𝓞 K))
        (SelmerChi := OldPrimal59 rho chi)
        (DOmegaSelmerChiStar := OldReflectedDual59 rho omega chi)
        rhoQ omega chi distinguishedPlace wild) :=
  ⟨core.toReflectedWildLocalizationAt59⟩

end ReflectedWildKummerCoreAt59

end Fermat.FiftyNine.Conservation.VostokovLocalization59
