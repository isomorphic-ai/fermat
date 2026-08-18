/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Fire the normalized continuous localization through the Ulam readout

The continuous Kummer construction supplies the complete localization-at-59
producer.  This file installs that producer in the existing Ulam endpoint,
so localization is no longer carried as an arithmetic hypothesis.  Pointed
Poitou--Tate incidence and Fourier seating also construct the nonzero boundary
receipt and the nonempty normalized fiber.

The remaining inputs stay visible: lawfulness on the conserved 827 kernel,
the class-valued relation-(7a) comparison, and global reciprocity.  In
particular this module neither collapses the fiber nor erases `ker G`.
-/
import Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.SelmerEigenspace
open CyclotomicSelmerAction59
open DetectorWitness827
open LocalCompletion59
open NormalizedContinuousWildLocalization59
open PointedTateIncidence
open SplitPrimeFourier827
open StateFactorPair
open TateBridge
open UlamReadout827
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩
local instance : Fact (0 < 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]
variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
variable (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The strict primal eigenspace inherits the exponent-59 law from its
ambient Kummer quotient. -/
theorem oldPrimal59_nsmul_eq_zero
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi) :
    59 • x = 0 := by
  apply Subtype.ext
  exact SelmerEigenspace.p_nsmul_eq_zero x.1

noncomputable local instance instOldPrimal59ModuleZMod :
    Module (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi) :=
  AddCommGroup.zmodModule (oldPrimal59_nsmul_eq_zero K chi)

/-- The carrier extension obtained from the unconditional normalized
continuous localization. -/
noncomputable def normalizedReflectedWildCarrierExtension59 :=
  (normalizedReflectedWildLocalization59 K omega chi)
    |>.toReflectedWildCarrierExtension827

@[simp]
theorem normalizedReflectedWildCarrierExtension59_reading
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi)
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    (normalizedReflectedWildCarrierExtension59 K omega chi).qRelaxedWild.reading
        x y =
      (normalizedReflectedWildLocalization59 K omega chi).readingAt59 x y :=
  rfl

/-- Pointed incidence and Fourier seating discharge the nonzero-boundary
premise for the canonical q-relaxed cyclotomic representation. -/
theorem normalizedBoundaryFunctional59_ne_zero
    (selectedPlace : Place827 K)
    (incidence : PointedTateIncidence827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (seating : QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace) :
    reflectedBoundaryFunctional827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        omega chi selectedPlace ≠ 0 :=
  reflectedBoundaryFunctional827_ne_zero
    (cyclotomicQRelaxedSelmerRepresentation827 K)
    omega chi selectedPlace incidence seating

/-- The same inputs retain the complete normalized fiber as a nonempty
public carrier. -/
theorem normalizedReflectedFiber59_nonempty
    (selectedPlace : Place827 K)
    (incidence : PointedTateIncidence827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (seating : QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace) :
    Nonempty (NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace) :=
  normalizedReflectedFiber827_nonempty
    (cyclotomicQRelaxedSelmerRepresentation827 K)
    omega chi selectedPlace incidence seating

/-- Lawfulness for the concrete carrier extension constructed from the
normalized continuous pairing.  This is still a genuine arithmetic
condition; the abbreviation only fixes the extension to which it applies. -/
abbrev NormalizedWildLawfulness59 (selectedPlace : Place827 K) :=
  WildLawfulness827
    (cyclotomicQRelaxedSelmerRepresentation827 K)
    omega chi selectedPlace (lambdaPlace59 K)
    (normalizedOldWildInterface59 K omega chi)
    (normalizedReflectedWildCarrierExtension59 K omega chi)

/-- Once pointed incidence and Fourier seating prove that the boundary is
nonzero, lawfulness produces the canonical scalar coefficient for the
normalized continuous wild pairing. -/
noncomputable def normalizedWildCoefficient59
    (selectedPlace : Place827 K)
    (incidence : PointedTateIncidence827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (seating : QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (lawful : NormalizedWildLawfulness59 K omega chi selectedPlace) :
    H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K) chi) →ₗ[ZMod 59] ZMod 59 :=
  wildCoefficient827
    (cyclotomicQRelaxedSelmerRepresentation827 K)
    omega chi selectedPlace (lambdaPlace59 K)
    (normalizedOldWildInterface59 K omega chi)
    (normalizedReflectedWildCarrierExtension59 K omega chi)
    (normalizedBoundaryFunctional59_ne_zero
      K omega chi selectedPlace incidence seating)
    lawful

/-- The normalized continuous reading is the canonical coefficient times
the conserved 827 boundary coordinate on every lawful carrier. -/
theorem normalizedWildCoefficient59_factorization
    (selectedPlace : Place827 K)
    (incidence : PointedTateIncidence827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (seating : QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (lawful : NormalizedWildLawfulness59 K omega chi selectedPlace)
    (h : H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K) chi))
    (y : QRelaxedReflectedDual827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    (normalizedReflectedWildCarrierExtension59 K omega chi).qRelaxedWild.reading
        h y =
      normalizedWildCoefficient59 K omega chi selectedPlace
          incidence seating lawful h *
        reflectedBoundaryFunctional827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          omega chi selectedPlace y :=
  qRelaxedWild_factorization
    (cyclotomicQRelaxedSelmerRepresentation827 K)
    omega chi selectedPlace (lambdaPlace59 K)
    (normalizedOldWildInterface59 K omega chi)
    (normalizedReflectedWildCarrierExtension59 K omega chi)
    (normalizedBoundaryFunctional59_ne_zero
      K omega chi selectedPlace incidence seating)
    lawful h y

/-- Reciprocity for the exact place-indexed pairing produced by the
normalized continuous localization.  It remains an explicit interface. -/
abbrev NormalizedTameSilenceReciprocity59 :=
  TameSilenceReciprocity827
    (cyclotomicQRelaxedSelmerRepresentation827 K)
    omega chi (lambdaPlace59 K)
    (normalizedOldWildInterface59 K omega chi)
    (normalizedReflectedWildLocalization59 K omega chi)

/-- For the normalized one-column localization, reciprocity itself proves
lawfulness on the conserved 827 kernel. -/
theorem normalizedWildLawfulness59_of_reciprocity
    (selectedPlace : Place827 K)
    (execution : NormalizedTameSilenceReciprocity59 K omega chi) :
    NormalizedWildLawfulness59 K omega chi selectedPlace :=
  wildLawfulness827_of_reciprocity
    (cyclotomicQRelaxedSelmerRepresentation827 K)
    omega chi selectedPlace (lambdaPlace59 K)
    (normalizedOldWildInterface59 K omega chi)
    (normalizedReflectedWildLocalization59 K omega chi)
    execution

/-- The canonical coefficient when lawfulness is obtained from reciprocity
rather than supplied separately. -/
noncomputable def normalizedWildCoefficientOfReciprocity59
    (selectedPlace : Place827 K)
    (incidence : PointedTateIncidence827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (seating : QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (execution : NormalizedTameSilenceReciprocity59 K omega chi) :
    H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K) chi) →ₗ[ZMod 59] ZMod 59 :=
  normalizedWildCoefficient59 K omega chi selectedPlace incidence seating
    (normalizedWildLawfulness59_of_reciprocity
      K omega chi selectedPlace execution)

variable {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
variable {solution : FermatState.PrimitiveSecondCaseSolution}
variable {hz : (59 : ℤ) ∣ solution.z}

/-- The Ulam relation-(7a) endpoint with the continuous Kummer localization,
the boundary proof, and a member of the retained normalized fiber all
constructed internally.  The remaining parameters are precisely the
lawfulness, class-gauge comparison, and reciprocity seams. -/
theorem vandiverSevenA_of_normalizedContinuousReadout
    (selectedPlace : Place827 K)
    (incidence : PointedTateIncidence827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (seating : QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (lawful : NormalizedWildLawfulness59 K omega chi selectedPlace)
    (pair : StateLinkedIdealPair hZeta solution hz)
    (hF : H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K) chi))
    (gaugeSeating : ClassValuedSevenAGaugeSeating pair hF)
    (processes : WildProcessesAtLeastSevenA gaugeSeating
      (normalizedWildCoefficient59 K omega chi selectedPlace
        incidence seating lawful))
    (execution : NormalizedTameSilenceReciprocity59 K omega chi) :
    pair.ledger.VandiverSevenA 0 1 := by
  let boundary_ne_zero := normalizedBoundaryFunctional59_ne_zero
    K omega chi selectedPlace incidence seating
  exact (normalizedReflectedFiber59_nonempty
    K omega chi selectedPlace incidence seating).elim fun y ↦
      vandiverSevenA_of_readout_interfaces
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        omega chi selectedPlace (lambdaPlace59 K)
        (normalizedOldWildInterface59 K omega chi)
        boundary_ne_zero
        (normalizedReflectedWildLocalization59 K omega chi)
        lawful pair hF gaugeSeating processes execution y

/-- Stronger compiled endpoint: for the normalized localization, global
reciprocity discharges lawfulness automatically.  The remaining arithmetic
comparison is exactly that the resulting wild coefficient processes the
class-valued relation-(7a) gauge. -/
theorem vandiverSevenA_of_normalizedContinuousReciprocity
    (selectedPlace : Place827 K)
    (incidence : PointedTateIncidence827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (seating : QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (pair : StateLinkedIdealPair hZeta solution hz)
    (hF : H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K) chi))
    (gaugeSeating : ClassValuedSevenAGaugeSeating pair hF)
    (execution : NormalizedTameSilenceReciprocity59 K omega chi)
    (processes : WildProcessesAtLeastSevenA gaugeSeating
      (normalizedWildCoefficientOfReciprocity59
        K omega chi selectedPlace incidence seating execution)) :
    pair.ledger.VandiverSevenA 0 1 :=
  vandiverSevenA_of_normalizedContinuousReadout
    K omega chi selectedPlace incidence seating
    (normalizedWildLawfulness59_of_reciprocity
      K omega chi selectedPlace execution)
    pair hF gaugeSeating processes execution

end Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59
