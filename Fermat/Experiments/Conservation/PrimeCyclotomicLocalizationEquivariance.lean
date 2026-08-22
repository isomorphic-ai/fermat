/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Prime-generic cyclotomic localization equivariance

For every prime `p`, this file reads supported Selmer localization in the
canonical cyclotomic orbit through a selected place.  Valuation covariance
and the actual cyclotomic Selmer representation show that an `eta`-eigenclass
has inverse-`eta` localization coordinates.  Applying this to the genuine
reflected-character projector packages the projected localization vector as
one pure residue-field character mode.

Cyclotomic stability only says that the orbit remains in the support.  It
does not imply that the orbit map is injective or surjective, so the generic
construction is honestly a map rather than an equivalence.  Regular orbit
equivalences remain the responsibility of arithmetic specializations.
-/
import Fermat.Experiments.Conservation.PrimeCyclotomicSelmerAction
import Fermat.Experiments.Conservation.PrimeResidueFourier

open scoped MonoidAlgebra nonZeroDivisors NumberField Pointwise

noncomputable section

namespace Fermat.Conservation.PrimeCyclotomicLocalizationEquivariance

open Fermat.Conservation.InvolutiveBase
open Fermat.Conservation.PrimeCyclotomicSelmerAction
open Fermat.Conservation.PrimeResidueFourier
open Fermat.Conservation.SelmerEigenspace

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

/-! ## The canonical orbit inside a stable support -/

/-- The cyclotomic orbit through one point of a stable support.  Stability
gives membership of every transported place but no regularity assertion. -/
noncomputable def cyclotomicSupportOrbitMap
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport p K S) (selected : S) :
    KummerCriterion.CyclotomicUnitDelta p → S :=
  fun sigma =>
    ⟨cyclotomicPlaceEquiv p K sigma selected.1,
      (hS sigma selected.1).mpr selected.2⟩

/-- Readback of the stable-support orbit on the underlying height-one
place. -/
@[simp]
theorem cyclotomicSupportOrbitMap_coe
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport p K S) (selected : S)
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    (cyclotomicSupportOrbitMap p K S hS selected sigma).1 =
      cyclotomicPlaceEquiv p K sigma selected.1 :=
  rfl

/-! ## Localization covariance on the actual eigenspace -/

/-- Localization of an actual cyclotomic `eta`-eigenclass transforms by the
inverse reduced character when the places are read in the positive
cyclotomic orbit order. -/
theorem eigenspaceSupportValuationAt_cyclotomicSupportOrbitMap
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport p K S)
    (eta : Character (PadicInt p)
      (KummerCriterion.CyclotomicUnitDelta p))
    (selected : S)
    (y : SelmerChiAt (cyclotomicSelmerRepresentationAt p K S hS) eta)
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    eigenspaceSupportValuationAt
        (cyclotomicSelmerRepresentationAt p K S hS) eta
        (cyclotomicSupportOrbitMap p K S hS selected sigma) y =
      (((reducedCharacterAt eta)⁻¹ sigma : (ZMod p)ˣ) : ZMod p) *
        eigenspaceSupportValuationAt
          (cyclotomicSelmerRepresentationAt p K S hS) eta selected y := by
  have heigen :=
    (mem_characterEigenspaceAt_iff
      (cyclotomicSelmerRepresentationAt p K S hS) eta y.1).mp
        y.property sigma⁻¹
  have hquot := congrArg
    (fun t : SelmerCarrierAt (𝓞 K) K S p => (Additive.toMul t).1) heigen
  change cyclotomicKummerHom p K sigma⁻¹ (Additive.toMul y.1).1 =
      (Additive.toMul ((eta sigma⁻¹ : PadicInt p) • y.1)).1 at hquot
  have hcov := cyclotomicValuationCovariance p K sigma⁻¹ selected.1
    (Additive.toMul y.1).1
  simp only [inv_inv] at hcov
  have hscalar := ZMod.map_smul
    (supportValuationAt
      (R := NumberField.RingOfIntegers K) (K := K) (p := p)
      (S := S) selected)
    (PadicInt.toZMod (eta sigma⁻¹ : PadicInt p)) y.1
  change
    Multiplicative.toAdd
        ((cyclotomicPlaceEquiv p K sigma selected.1).valuationOfNeZeroMod p
          (Additive.toMul y.1).1) = _
  rw [← hcov, hquot]
  change supportValuationAt
      (R := NumberField.RingOfIntegers K) (K := K) (p := p)
      (S := S) selected
        ((eta sigma⁻¹ : PadicInt p) • y.1) = _
  rw [padicInt_smul_eq_toZMod_smul, hscalar]
  change PadicInt.toZMod (eta sigma⁻¹ : PadicInt p) *
      supportValuationAt
        (R := NumberField.RingOfIntegers K) (K := K) (p := p)
        (S := S) selected y.1 =
    (((reducedCharacterAt eta)⁻¹ sigma : (ZMod p)ˣ) : ZMod p) *
      supportValuationAt
        (R := NumberField.RingOfIntegers K) (K := K) (p := p)
        (S := S) selected y.1
  simp

/-! ## The projected reflected localization vector -/

section Projected

variable [Invertible
  (Fintype.card (KummerCriterion.CyclotomicUnitDelta p) : PadicInt p)]

/-- Supported localization after the genuine reflected-character projector,
read in the canonical cyclotomic orbit through `selected`. -/
noncomputable def cyclotomicProjectedLocalizationVectorAt
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport p K S)
    (omega chi : Character (PadicInt p)
      (KummerCriterion.CyclotomicUnitDelta p))
    (selected : S) (source : SelmerCarrierAt (𝓞 K) K S p) :
    KummerCriterion.CyclotomicUnitDelta p → ZMod p :=
  fun sigma =>
    eigenspaceSupportValuationAt
      (cyclotomicSelmerRepresentationAt p K S hS)
      (reflectedCharacter omega chi)
      (cyclotomicSupportOrbitMap p K S hS selected sigma)
      (characterProjectorAt
        (cyclotomicSelmerRepresentationAt p K S hS)
        (reflectedCharacter omega chi) source)

/-- Evaluation of the projected localization vector is the corresponding
supported valuation coordinate. -/
@[simp]
theorem cyclotomicProjectedLocalizationVectorAt_apply
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport p K S)
    (omega chi : Character (PadicInt p)
      (KummerCriterion.CyclotomicUnitDelta p))
    (selected : S) (source : SelmerCarrierAt (𝓞 K) K S p)
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    cyclotomicProjectedLocalizationVectorAt p K S hS omega chi
        selected source sigma =
      eigenspaceSupportValuationAt
        (cyclotomicSelmerRepresentationAt p K S hS)
        (reflectedCharacter omega chi)
        (cyclotomicSupportOrbitMap p K S hS selected sigma)
        (characterProjectorAt
          (cyclotomicSelmerRepresentationAt p K S hS)
          (reflectedCharacter omega chi) source) :=
  rfl

/-- The projected vector transforms by the inverse reduced reflected
character. -/
theorem cyclotomicProjectedLocalizationVectorAt_orbit
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport p K S)
    (omega chi : Character (PadicInt p)
      (KummerCriterion.CyclotomicUnitDelta p))
    (selected : S) (source : SelmerCarrierAt (𝓞 K) K S p)
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    cyclotomicProjectedLocalizationVectorAt p K S hS omega chi
        selected source sigma =
      (((reducedCharacterAt (reflectedCharacter omega chi))⁻¹ sigma :
          (ZMod p)ˣ) : ZMod p) *
        eigenspaceSupportValuationAt
          (cyclotomicSelmerRepresentationAt p K S hS)
          (reflectedCharacter omega chi) selected
          (characterProjectorAt
            (cyclotomicSelmerRepresentationAt p K S hS)
            (reflectedCharacter omega chi) source) :=
  eigenspaceSupportValuationAt_cyclotomicSupportOrbitMap
    p K S hS (reflectedCharacter omega chi) selected
    (characterProjectorAt
      (cyclotomicSelmerRepresentationAt p K S hS)
      (reflectedCharacter omega chi) source) sigma

/-- The projected localization vector is one pure inverse
reflected-character mode over `ZMod p`. -/
theorem cyclotomicProjectedLocalizationVectorAt_isPureCharacter
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport p K S)
    (omega chi : Character (PadicInt p)
      (KummerCriterion.CyclotomicUnitDelta p))
    (selected : S) (source : SelmerCarrierAt (𝓞 K) K S p) :
    IsPureCharacter
      ((reducedCharacterAt (reflectedCharacter omega chi))⁻¹)
      (cyclotomicProjectedLocalizationVectorAt p K S hS omega chi
        selected source) := by
  let eta := reflectedCharacter omega chi
  let psi := (reducedCharacterAt eta)⁻¹
  let component := eigenspaceSupportValuationAt
    (cyclotomicSelmerRepresentationAt p K S hS) eta selected
    (characterProjectorAt
      (cyclotomicSelmerRepresentationAt p K S hS) eta source)
  refine ⟨component, ?_⟩
  funext sigma
  change cyclotomicProjectedLocalizationVectorAt p K S hS omega chi
      selected source sigma = component * (psi sigma : ZMod p)
  rw [mul_comm]
  exact cyclotomicProjectedLocalizationVectorAt_orbit
    p K S hS omega chi selected source sigma

end Projected

end Fermat.Conservation.PrimeCyclotomicLocalizationEquivariance
