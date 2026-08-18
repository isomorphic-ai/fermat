/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Restrict the continuous Kummer pairing to the old wild interface

`WildLocalInterface` contains only a bilinear reading on the two seated
Selmer eigenspaces and its integral-group-algebra adjoint law.  Any total
pairing on the ambient Kummer quotient therefore restricts to such an
interface: on the two fixed character seats the adjoint law is formal.

This direction is important.  The quotient pairing is not reconstructed
from an old reading.  Instead the newly constructed pairing is restricted to
the old carrier shape, so its calibration equation is definitional.  This
does not identify the resulting interface with an independently supplied
historical `OldWildInterface59`; that stronger comparison remains precisely
the old-reading calibration theorem.

Finally, the unconditional normalized-readout existence theorem supplies a
total continuous Kummer pairing, hence an old-shaped wild interface and a
fully calibrated reflected wild core.
-/
import Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59
import Fermat.FiftyNine.Conservation.NormImageConsequences59

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59

open Fermat.Conservation
open Fermat.Conservation.ContinuousCyclicH2Readout59
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TamePlacePairing
open Fermat.Conservation.WildKummerPairing
open CyclotomicSelmerAction59
open ContinuousKummerTateLocalization59
open EmptySupportReflectedInclusion827
open LocalCompletion59
open NormImageConsequences59
open SplitPrimeFourier827
open TwistedLambdaH2Inflation59
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩
local instance : Fact (0 < 59) := ⟨by decide⟩

variable {K : Type} [Field K] [NumberField K]
  (rho : SelmerDeltaRepresentation
    (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
    (Delta := GaloisIndex59))
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

/-- Restrict a total Kummer-quotient pairing to the two old seated Selmer
carriers. -/
def oldReadingOfPairing (pairing : Pairing 59 K) :
    OldPrimal59 rho chi →+ (OldReflectedDual59 rho omega chi →+ ZMod 59) :=
  AddMonoidHom.compl₂
    (pairing.comp (toKummerClass (rho := rho) (chi := chi)))
    (toKummerClass
      (rho := rho) (chi := InvolutiveBase.reflectedCharacter omega chi))

@[simp]
theorem oldReadingOfPairing_apply
    (pairing : Pairing 59 K)
    (x : OldPrimal59 rho chi)
    (y : OldReflectedDual59 rho omega chi) :
    oldReadingOfPairing rho omega chi pairing x y =
      pairing (toKummerClass x) (toKummerClass y) :=
  rfl

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

private theorem hash_single_smul_oldReflected
    (delta : GaloisIndex59) (c : PadicInt 59)
    (y : OldReflectedDual59 rho omega chi) :
    InvolutiveBase.hash omega (MonoidAlgebra.single delta c) • y =
      (c * (chi delta : PadicInt 59)) • y := by
  rw [InvolutiveBase.hash_apply_single]
  have hdelta :
      characterEigenspaceRepresentation rho
          (InvolutiveBase.reflectedCharacter omega chi) delta⁻¹ y =
        (InvolutiveBase.reflectedCharacter omega chi delta⁻¹ :
          PadicInt 59) • y := by
    apply Subtype.ext
    exact (mem_characterEigenspace_iff rho
      (InvolutiveBase.reflectedCharacter omega chi) y.1).mp
        y.property delta⁻¹
  calc
    MonoidAlgebra.single delta⁻¹ (c * (omega delta : PadicInt 59)) • y =
        (c * (omega delta : PadicInt 59)) •
          characterEigenspaceRepresentation rho
            (InvolutiveBase.reflectedCharacter omega chi) delta⁻¹ y := by
      change ((characterEigenspaceRepresentation rho
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

private theorem oldReadingOfPairing_single_adjoint
    (pairing : Pairing 59 K)
    (delta : GaloisIndex59) (c : PadicInt 59)
    (x : OldPrimal59 rho chi)
    (y : OldReflectedDual59 rho omega chi) :
    oldReadingOfPairing rho omega chi pairing
        (MonoidAlgebra.single delta c • x) y =
      oldReadingOfPairing rho omega chi pairing x
        (InvolutiveBase.hash omega (MonoidAlgebra.single delta c) • y) := by
  rw [single_smul_oldPrimal, hash_single_smul_oldReflected]
  change pairing
      (toKummerClass ((c * (chi delta : PadicInt 59)) • x))
      (toKummerClass y) =
    pairing (toKummerClass x)
      (toKummerClass ((c * (chi delta : PadicInt 59)) • y))
  change pairing
      ((PadicInt.toZMod (c * (chi delta : PadicInt 59))).val •
        toKummerClass x)
      (toKummerClass y) =
    pairing (toKummerClass x)
      ((PadicInt.toZMod (c * (chi delta : PadicInt 59))).val •
        toKummerClass y)
  rw [map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply]

/-- The `hash omega` adjoint law of the restricted pairing is forced by the
two character seats; it requires no extra arithmetic property of the total
Kummer pairing. -/
theorem oldReadingOfPairing_adjoint
    (pairing : Pairing 59 K)
    (a : IntegralPadicGroupAlgebra 59 GaloisIndex59)
    (x : OldPrimal59 rho chi)
    (y : OldReflectedDual59 rho omega chi) :
    oldReadingOfPairing rho omega chi pairing (a • x) y =
      oldReadingOfPairing rho omega chi pairing x
        ((InvolutiveBase.hash omega a) • y) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero =>
      simp only [zero_smul, map_zero, AddMonoidHom.zero_apply]
  | add a b ha hb =>
      calc
        oldReadingOfPairing rho omega chi pairing ((a + b) • x) y =
            oldReadingOfPairing rho omega chi pairing (a • x + b • x) y := by
          rw [add_smul]
        _ = oldReadingOfPairing rho omega chi pairing (a • x) y +
            oldReadingOfPairing rho omega chi pairing (b • x) y := by
          rw [map_add, AddMonoidHom.add_apply]
        _ = oldReadingOfPairing rho omega chi pairing x
              ((InvolutiveBase.hash omega a) • y) +
            oldReadingOfPairing rho omega chi pairing x
              ((InvolutiveBase.hash omega b) • y) := by
          rw [ha, hb]
        _ = oldReadingOfPairing rho omega chi pairing x
            ((InvolutiveBase.hash omega a) • y +
              (InvolutiveBase.hash omega b) • y) := by rw [map_add]
        _ = oldReadingOfPairing rho omega chi pairing x
            (((InvolutiveBase.hash omega a) +
              (InvolutiveBase.hash omega b)) • y) := by rw [add_smul]
        _ = oldReadingOfPairing rho omega chi pairing x
            ((InvolutiveBase.hash omega (a + b)) • y) := by
          exact congrArg
            (fun z : IntegralPadicGroupAlgebra 59 GaloisIndex59 ↦
              oldReadingOfPairing rho omega chi pairing x (z • y))
            (map_add (InvolutiveBase.hash omega) a b).symm
  | single delta c =>
      exact oldReadingOfPairing_single_adjoint rho omega chi pairing
        delta c x y

/-- The actual old-interface constructor obtained by restriction of a total
Kummer pairing. -/
def oldWildInterfaceOfPairing
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (pairing : Pairing 59 K) :
    OldWildInterface59 rho omega chi distinguishedPlace where
  reading := oldReadingOfPairing rho omega chi pairing
  adjoint_law := oldReadingOfPairing_adjoint rho omega chi pairing

@[simp]
theorem oldWildInterfaceOfPairing_reading
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (pairing : Pairing 59 K)
    (x : OldPrimal59 rho chi)
    (y : OldReflectedDual59 rho omega chi) :
    (oldWildInterfaceOfPairing rho omega chi distinguishedPlace pairing).reading
        x y = pairing (toKummerClass x) (toKummerClass y) :=
  rfl

/-- Restricting a pairing and then calibrating that same pairing against the
resulting interface is definitional. -/
theorem pairing_calibrates_oldWildInterfaceOfPairing
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (pairing : Pairing 59 K)
    (x : OldPrimal59 rho chi)
    (y : OldReflectedDual59 rho omega chi) :
    pairing (toKummerClass x) (toKummerClass y) =
      (oldWildInterfaceOfPairing rho omega chi distinguishedPlace pairing).reading
        x y :=
  rfl

/-- For an independently supplied historical interface, the old calibration
is exactly the proposition that it equals the interface obtained by
restricting the quotient pairing.  Thus restriction closes calibration for
the constructed interface, but cannot manufacture comparison with a separate
old arithmetic reading. -/
theorem oldWildInterfaceOfPairing_eq_iff_calibration
    (distinguishedPlace : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (pairing : Pairing 59 K)
    (wild : OldWildInterface59 rho omega chi distinguishedPlace) :
    oldWildInterfaceOfPairing rho omega chi distinguishedPlace pairing = wild ↔
      ∀ x : OldPrimal59 rho chi,
        ∀ y : OldReflectedDual59 rho omega chi,
          pairing (toKummerClass x) (toKummerClass y) =
            wild.reading x y := by
  constructor
  · rintro rfl x y
    rfl
  · intro hcalibration
    cases wild with
    | mk reading adjoint_law =>
        have hreading : oldReadingOfPairing rho omega chi pairing = reading := by
          ext x y
          exact hcalibration x y
        subst reading
        rfl

/-! ## The unconditional normalized continuous specialization -/

variable [IsCyclotomicExtension {59} ℚ K]

/-- The old-shaped interface cut out by the actual continuous Kummer cup and
a supplied scalar readout. -/
def continuousOldWildInterface59
    (readout : LambdaContinuousH2Readout59 K)
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    OldWildInterface59 (cyclotomicStrictSelmerRepresentation59 K)
      omega chi (lambdaPlace59 K) :=
  oldWildInterfaceOfPairing (cyclotomicStrictSelmerRepresentation59 K)
    omega chi (lambdaPlace59 K) (lambdaGlobalPairing K readout)

@[simp]
theorem continuousOldWildInterface59_reading
    (readout : LambdaContinuousH2Readout59 K)
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : OldReflectedDual59
      (cyclotomicStrictSelmerRepresentation59 K) omega chi) :
    (continuousOldWildInterface59 (K := K) readout omega chi).reading x y =
      lambdaGlobalPairing K readout (toKummerClass x) (toKummerClass y) :=
  rfl

/-- With the interface constructed from the continuous pairing, the complete
canonical reflected wild core has no separate calibration premise. -/
def continuousReflectedWildKummerCoreAt59
    (readout : LambdaContinuousH2Readout59 K)
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    ReflectedWildKummerCoreAt59
      (cyclotomicStrictSelmerRepresentation59 K)
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi (lambdaPlace59 K)
      (continuousOldWildInterface59 (K := K) readout omega chi) where
  pairing := lambdaGlobalPairing K readout
  landing := cyclotomicReflectedEmptySupportLanding827 K omega chi
  old_calibration := fun _ _ ↦ rfl

@[simp]
theorem continuousReflectedWildKummerCoreAt59_pairing
    (readout : LambdaContinuousH2Readout59 K)
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    (continuousReflectedWildKummerCoreAt59 (K := K) readout omega chi).pairing =
      lambdaGlobalPairing K readout :=
  rfl

/-- Feed the self-calibrated continuous core directly into the actual
q-relaxed localization consumer. -/
def continuousReflectedWildLocalizationAt59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (readout : LambdaContinuousH2Readout59 K)
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    UlamReadout827.ReflectedWildLocalizationAt59
      (Place := IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K))
      (SelmerChi := OldPrimal59
        (cyclotomicStrictSelmerRepresentation59 K) chi)
      (DOmegaSelmerChiStar := OldReflectedDual59
        (cyclotomicStrictSelmerRepresentation59 K) omega chi)
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi (lambdaPlace59 K)
      (continuousOldWildInterface59 (K := K) readout omega chi) :=
  (continuousReflectedWildKummerCoreAt59 (K := K) readout omega chi).toReflectedWildLocalizationAt59

/-- The norm-image theorem supplies a normalized readout, so the continuous
pairing unconditionally yields an old-shaped interface and its calibrated
wild core.  The witness readout is noncanonical; no equality with a separately
supplied historical interface is asserted. -/
theorem exists_normalizedContinuousReflectedWildKummerCoreAt59
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    ∃ readout : LambdaContinuousH2Readout59 K,
      readout.comp (twistedLambdaH2Inflation59 K) =
          actualContinuousCyclicH2Readout59 ∧
        Nonempty
          (ReflectedWildKummerCoreAt59
            (cyclotomicStrictSelmerRepresentation59 K)
            (cyclotomicQRelaxedSelmerRepresentation827 K)
            omega chi (lambdaPlace59 K)
            (continuousOldWildInterface59 (K := K) readout omega chi)) := by
  obtain ⟨readout, hnormalized⟩ := exists_normalizedInflationReadout59 K
  exact ⟨readout, hnormalized,
    ⟨continuousReflectedWildKummerCoreAt59 (K := K) readout omega chi⟩⟩

/-- Unconditional normalized-readout package at the first real downstream
consumer: the q-relaxed localization producer itself is inhabited. -/
theorem exists_normalizedContinuousReflectedWildLocalizationAt59
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    ∃ readout : LambdaContinuousH2Readout59 K,
      readout.comp (twistedLambdaH2Inflation59 K) =
          actualContinuousCyclicH2Readout59 ∧
        Nonempty
          (UlamReadout827.ReflectedWildLocalizationAt59
            (Place := IsDedekindDomain.HeightOneSpectrum
              (NumberField.RingOfIntegers K))
            (SelmerChi := OldPrimal59
              (cyclotomicStrictSelmerRepresentation59 K) chi)
            (DOmegaSelmerChiStar := OldReflectedDual59
              (cyclotomicStrictSelmerRepresentation59 K) omega chi)
            (cyclotomicQRelaxedSelmerRepresentation827 K)
            omega chi (lambdaPlace59 K)
            (continuousOldWildInterface59 (K := K) readout omega chi)) := by
  obtain ⟨readout, hnormalized⟩ := exists_normalizedInflationReadout59 K
  exact ⟨readout, hnormalized,
    ⟨continuousReflectedWildLocalizationAt59 (K := K) readout omega chi⟩⟩

end Fermat.FiftyNine.Conservation.ContinuousOldWildAdapter59
