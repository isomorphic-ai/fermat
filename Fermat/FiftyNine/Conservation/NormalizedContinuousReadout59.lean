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

The strongest endpoint derives pointed incidence from a concrete reflected
lift plus Fourier seating, and derives lawfulness from reciprocity.  The
present one-column reciprocity interface also annihilates the resulting wild
coefficient.  Consequently its `processes at least 7a` input is proved below
to be equivalent to vanishing of the complete class-valued gauge map.  The
endpoint remains a useful type-correct diagnostic, but is not presented as a
non-circular proof of relation (7a).  This module neither collapses the fiber
nor erases `ker G`.
-/
import Fermat.FiftyNine.Conservation.AlgebraicPointedIncidence827
import Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827
import Fermat.FiftyNine.Conservation.NormalizedContinuousWildLocalization59

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.Conservation.SelmerEigenspace
open AlgebraicPointedIncidence827
open CyclotomicLocalizationEquivariance827
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

/-- The canonical cyclotomic q-relaxed representation supplies its own
Fourier seating at every selected place above 827. -/
theorem normalizedQLocalizationEquivariance827
    (selectedPlace : Place827 K) :
    QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi selectedPlace :=
  cyclotomicQLocalizationEquivariance827 K omega chi selectedPlace

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

/-- The coefficient produced from the present one-column reciprocity
interface is the zero map.  Keeping this theorem explicit prevents a later
consumer from mistaking reciprocity-derived lawfulness for a nonzero wild
readout. -/
theorem normalizedWildCoefficientOfReciprocity59_eq_zero
    (selectedPlace : Place827 K)
    (incidence : PointedTateIncidence827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (seating : QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (execution : NormalizedTameSilenceReciprocity59 K omega chi) :
    normalizedWildCoefficientOfReciprocity59
        K omega chi selectedPlace incidence seating execution = 0 := by
  simpa [normalizedWildCoefficientOfReciprocity59,
    normalizedWildCoefficient59, normalizedReflectedWildCarrierExtension59]
    using wildCoefficient827_eq_zero_of_reciprocity
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi selectedPlace (lambdaPlace59 K)
      (normalizedOldWildInterface59 K omega chi)
      (normalizedBoundaryFunctional59_ne_zero
        K omega chi selectedPlace incidence seating)
      (normalizedReflectedWildLocalization59 K omega chi)
      execution

/-- A concrete reflected lift and Fourier seating construct the pointed
incidence used by the normalized readout. -/
noncomputable def normalizedPointedIncidence59OfLift
    (lift : ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (seating : QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi lift.selectedPlace) :
    PointedTateIncidence827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi lift.selectedPlace :=
  pointedTateIncidence827_of_fourierSeating_of_lift
    (cyclotomicQRelaxedSelmerRepresentation827 K)
    omega chi lift seating

/-- Pointed incidence from a reflected lift alone: canonical cyclotomic
localization equivariance now supplies the former seating argument. -/
noncomputable def normalizedPointedIncidence59OfLiftCanonical
    (lift : ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) :
    PointedTateIncidence827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi lift.selectedPlace :=
  normalizedPointedIncidence59OfLift K omega chi lift
    (normalizedQLocalizationEquivariance827
      K omega chi lift.selectedPlace)

/-- The normalized wild coefficient with both lawfulness and pointed
incidence derived from reciprocity, Fourier seating, and the concrete lift. -/
noncomputable def normalizedWildCoefficientOfLift59
    (lift : ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (seating : QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi lift.selectedPlace)
    (execution : NormalizedTameSilenceReciprocity59 K omega chi) :
    H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K) chi) →ₗ[ZMod 59] ZMod 59 :=
  normalizedWildCoefficientOfReciprocity59
    K omega chi lift.selectedPlace
    (normalizedPointedIncidence59OfLift K omega chi lift seating)
    seating execution

/-- The lift-facing spelling of the same zero-coefficient boundary. -/
theorem normalizedWildCoefficientOfLift59_eq_zero
    (lift : ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (seating : QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi lift.selectedPlace)
    (execution : NormalizedTameSilenceReciprocity59 K omega chi) :
    normalizedWildCoefficientOfLift59
        K omega chi lift seating execution = 0 :=
  normalizedWildCoefficientOfReciprocity59_eq_zero
    K omega chi lift.selectedPlace
    (normalizedPointedIncidence59OfLift K omega chi lift seating)
    seating execution

/-- The normalized coefficient constructed from a reflected lift with
canonical Fourier seating. -/
noncomputable def normalizedWildCoefficientOfCanonicalLift59
    (lift : ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (execution : NormalizedTameSilenceReciprocity59 K omega chi) :
    H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K) chi) →ₗ[ZMod 59] ZMod 59 :=
  normalizedWildCoefficientOfLift59 K omega chi lift
    (normalizedQLocalizationEquivariance827
      K omega chi lift.selectedPlace)
    execution

/-- Canonical seating does not alter the zero-coefficient consequence of
the present one-column reciprocity interface. -/
theorem normalizedWildCoefficientOfCanonicalLift59_eq_zero
    (lift : ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (execution : NormalizedTameSilenceReciprocity59 K omega chi) :
    normalizedWildCoefficientOfCanonicalLift59
        K omega chi lift execution = 0 :=
  normalizedWildCoefficientOfLift59_eq_zero K omega chi lift
    (normalizedQLocalizationEquivariance827
      K omega chi lift.selectedPlace)
    execution

variable {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
variable {solution : FermatState.PrimitiveSecondCaseSolution}
variable {hz : (59 : ℤ) ∣ solution.z}

/-- Under the current one-column reciprocity interface, the normalized
`processes at least 7a` premise is exactly the stronger assertion that the
entire class-valued gauge map is zero. -/
theorem normalizedProcessesAtLeastSevenA_iff_gauge_eq_zero
    (selectedPlace : Place827 K)
    (incidence : PointedTateIncidence827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (seating : QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selectedPlace)
    (pair : StateLinkedIdealPair hZeta solution hz)
    (hF : H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K) chi))
    (gaugeSeating : ClassValuedSevenAGaugeSeating pair hF)
    (execution : NormalizedTameSilenceReciprocity59 K omega chi) :
    WildProcessesAtLeastSevenA gaugeSeating
        (normalizedWildCoefficientOfReciprocity59
          K omega chi selectedPlace incidence seating execution) ↔
      gaugeSeating.gauge = 0 := by
  rw [normalizedWildCoefficientOfReciprocity59_eq_zero]
  exact wildProcessesAtLeastSevenA_zero_iff gaugeSeating

/-- Lift-facing spelling of the exact same proof boundary. -/
theorem normalizedLiftProcessesAtLeastSevenA_iff_gauge_eq_zero
    (lift : ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (seating : QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi lift.selectedPlace)
    (pair : StateLinkedIdealPair hZeta solution hz)
    (hF : H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K) chi))
    (gaugeSeating : ClassValuedSevenAGaugeSeating pair hF)
    (execution : NormalizedTameSilenceReciprocity59 K omega chi) :
    WildProcessesAtLeastSevenA gaugeSeating
        (normalizedWildCoefficientOfLift59
          K omega chi lift seating execution) ↔
      gaugeSeating.gauge = 0 := by
  rw [normalizedWildCoefficientOfLift59_eq_zero]
  exact wildProcessesAtLeastSevenA_zero_iff gaugeSeating

/-- With canonical Fourier seating, a reflected lift is the only geometric
input left in the zero-coefficient diagnostic. -/
theorem normalizedCanonicalLiftProcessesAtLeastSevenA_iff_gauge_eq_zero
    (lift : ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (pair : StateLinkedIdealPair hZeta solution hz)
    (hF : H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K) chi))
    (gaugeSeating : ClassValuedSevenAGaugeSeating pair hF)
    (execution : NormalizedTameSilenceReciprocity59 K omega chi) :
    WildProcessesAtLeastSevenA gaugeSeating
        (normalizedWildCoefficientOfCanonicalLift59
          K omega chi lift execution) ↔
      gaugeSeating.gauge = 0 := by
  rw [normalizedWildCoefficientOfCanonicalLift59_eq_zero]
  exact wildProcessesAtLeastSevenA_zero_iff gaugeSeating

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
reciprocity discharges lawfulness automatically.  Because that same
one-column reciprocity makes the coefficient zero, the `processes` argument
here is equivalent to vanishing of the entire gauge map, as recorded by
`normalizedProcessesAtLeastSevenA_iff_gauge_eq_zero`. -/
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

/-- Strongest lift-facing endpoint in this module: the concrete reflected
q-relaxed lift replaces the independent pointed-incidence premise, while
reciprocity replaces the independent lawfulness premise.  It retains the
explicit circularity diagnostic: its `processes` input is equivalent to
vanishing of the whole gauge map. -/
theorem vandiverSevenA_of_normalizedContinuousLift
    (lift : ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (seating : QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      omega chi lift.selectedPlace)
    (pair : StateLinkedIdealPair hZeta solution hz)
    (hF : H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K) chi))
    (gaugeSeating : ClassValuedSevenAGaugeSeating pair hF)
    (execution : NormalizedTameSilenceReciprocity59 K omega chi)
    (processes : WildProcessesAtLeastSevenA gaugeSeating
      (normalizedWildCoefficientOfLift59
        K omega chi lift seating execution)) :
    pair.ledger.VandiverSevenA 0 1 :=
  vandiverSevenA_of_normalizedContinuousReciprocity
    K omega chi lift.selectedPlace
    (normalizedPointedIncidence59OfLift K omega chi lift seating)
    seating pair hF gaugeSeating execution processes

/-- Canonically seated lift-facing endpoint.  The reflected lift now
supplies all geometric data: cyclotomic covariance constructs Fourier
seating, and seating plus the lift constructs pointed incidence.  The
remaining `processes` input is still exactly whole-gauge vanishing under the
one-column reciprocity interface; this theorem removes a premise without
hiding that circularity. -/
theorem vandiverSevenA_of_normalizedContinuousCanonicalLift
    (lift : ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi)
    (pair : StateLinkedIdealPair hZeta solution hz)
    (hF : H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K) chi))
    (gaugeSeating : ClassValuedSevenAGaugeSeating pair hF)
    (execution : NormalizedTameSilenceReciprocity59 K omega chi)
    (processes : WildProcessesAtLeastSevenA gaugeSeating
      (normalizedWildCoefficientOfCanonicalLift59
        K omega chi lift execution)) :
    pair.ledger.VandiverSevenA 0 1 :=
  vandiverSevenA_of_normalizedContinuousLift
    K omega chi lift
    (normalizedQLocalizationEquivariance827
      K omega chi lift.selectedPlace)
    pair hF gaugeSeating execution processes

end Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59
