/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Canonical cyclotomic localization equivariance above 827

This file closes the arithmetic seating premise used by the 827-place
Fourier argument for the canonical cyclotomic q-relaxed representation.

First, the regular orbit order from `indexedPlaceOrbitEquiv827` is shown to
be the literal cyclotomic place action from `cyclotomicPlaceEquiv59`.  The
two constructions use the same inverse of Mathlib's `galEquivZMod`; the only
adapter needed is equality between Mathlib's integral Galois restriction and
the ring-of-integers equivalence used by the canonical Selmer action.

Then valuation covariance is applied to `sigma⁻¹`.  Its transported place
is therefore `sigma * selected`, while the reflected eigenspace law scales
the class by the `sigma⁻¹` reflected eigenvalue.  Reduction modulo 59 gives
exactly the inverse reflected Fourier character required by
`QLocalizationEquivariance827`.
-/
import Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
import Fermat.FiftyNine.Conservation.SplitPrimeFourier827

open scoped MonoidAlgebra nonZeroDivisors NumberField Pointwise

noncomputable section

namespace Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- Mathlib's restriction of a cyclotomic Galois automorphism to the ring of
integers is the same ring equivalence used by the canonical Selmer action. -/
private theorem galRestrict_eq_cyclotomicRingOfIntegersEquiv59
    (sigma : GaloisIndex59) :
    (galRestrict ℤ ℚ K (NumberField.RingOfIntegers K)
      ((IsCyclotomicExtension.Rat.galEquivZMod 59 K).symm sigma)).toRingEquiv =
      KummerCriterion.cyclotomicRingOfIntegersEquiv (p := 59) K sigma := by
  apply RingEquiv.ext
  intro x
  apply (FaithfulSMul.algebraMap_injective
    (NumberField.RingOfIntegers K) K)
  change algebraMap (NumberField.RingOfIntegers K) K
      (galRestrict ℤ ℚ K (NumberField.RingOfIntegers K)
        ((IsCyclotomicExtension.Rat.galEquivZMod 59 K).symm sigma) x) = _
  rw [algebraMap_galRestrict_apply]
  change
    ((IsCyclotomicExtension.Rat.galEquivZMod 59 K).symm sigma)
        (algebraMap (NumberField.RingOfIntegers K) K x) =
      algebraMap (NumberField.RingOfIntegers K) K
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := 59) K sigma x)
  rw [KummerCriterion.cyclotomicRingOfIntegersEquiv]
  exact (algebraMap.coe_smul'
    ((IsCyclotomicExtension.Rat.galEquivZMod 59 K).symm sigma) x K).symm

/-- Readback of the Galois orbit equivalence on underlying prime ideals. -/
private theorem placeOrbitEquiv827_asIdeal
    (selected : Place827 K) (tau : Gal(K/ℚ)) :
    ((placeOrbitEquiv827 K selected tau).1).asIdeal =
      Ideal.map
        (galRestrict ℤ ℚ K (NumberField.RingOfIntegers K) tau)
        selected.1.asIdeal := by
  rfl

/-- The regular 827-place orbit and the canonical cyclotomic place action
have the same orientation. -/
theorem indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59
    (selected : Place827 K) (sigma : GaloisIndex59) :
    (indexedPlaceOrbitEquiv827 K selected sigma).1 =
      cyclotomicPlaceEquiv59 K sigma selected.1 := by
  apply IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
  change ((placeOrbitEquiv827 K selected
      ((IsCyclotomicExtension.Rat.galEquivZMod 59 K).symm sigma)).1).asIdeal =
    Ideal.comap
      (KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := 59) K sigma).symm selected.1.asIdeal
  rw [placeOrbitEquiv827_asIdeal]
  rw [Ideal.comap_symm
    (KummerCriterion.cyclotomicRingOfIntegersEquiv (p := 59) K sigma)]
  change Ideal.map
      (galRestrict ℤ ℚ K (NumberField.RingOfIntegers K)
        ((IsCyclotomicExtension.Rat.galEquivZMod 59 K).symm sigma)).toRingEquiv.toRingHom
        selected.1.asIdeal =
    Ideal.map
      (KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := 59) K sigma).toRingHom selected.1.asIdeal
  rw [galRestrict_eq_cyclotomicRingOfIntegersEquiv59]

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

set_option maxRecDepth 2000 in
/-- Supported localization for the canonical q-relaxed cyclotomic
representation is contragredient-equivariant in the regular 827-place orbit
order.  This supplies the previously open Fourier seating premise. -/
theorem cyclotomicQLocalizationEquivariance827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (selected : Place827 K) :
    QLocalizationEquivariance827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi selected := by
  refine ⟨?_⟩
  intro sigma source
  let eta := InvolutiveBase.reflectedCharacter omega chi
  let y := qRelaxedReflectedProjector827
    (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi source
  have horbit :
      indexedPlaceOrbitEquiv827 K selected sigma =
        ⟨cyclotomicPlaceEquiv59 K sigma selected.1,
          (cyclotomicPlaceEquiv59_mem_placesOver827_iff
            K sigma selected.1).mpr selected.2⟩ := by
    apply Subtype.ext
    exact indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59 K selected sigma
  rw [horbit]
  have heigen :=
    (mem_characterEigenspaceAt_iff
      (cyclotomicQRelaxedSelmerRepresentation827 K) eta y.1).mp
        y.property sigma⁻¹
  have hquot := congrArg
    (fun t : QRelaxedSelmerCarrier827 K ↦ (Additive.toMul t).1) heigen
  change cyclotomicKummerHom59 K sigma⁻¹ (Additive.toMul y.1).1 =
      (Additive.toMul ((eta sigma⁻¹ : PadicInt 59) • y.1)).1 at hquot
  have hcov := cyclotomicValuationCovariance59 K sigma⁻¹ selected.1
    (Additive.toMul y.1).1
  simp only [inv_inv] at hcov
  have hscalar := ZMod.map_smul
    (supportValuationAt
      (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
      (S := placesOver827 K) selected)
    (PadicInt.toZMod (eta sigma⁻¹ : PadicInt 59)) y.1
  change
    Multiplicative.toAdd
        ((cyclotomicPlaceEquiv59 K sigma selected.1).valuationOfNeZeroMod 59
          (Additive.toMul y.1).1) = _
  rw [← hcov, hquot]
  change supportValuationAt
      (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
      (S := placesOver827 K) selected
        ((eta sigma⁻¹ : PadicInt 59) • y.1) = _
  rw [padicInt_smul_eq_toZMod_smul, hscalar]
  change PadicInt.toZMod (eta sigma⁻¹ : PadicInt 59) *
      supportValuationAt
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (S := placesOver827 K) selected y.1 =
    (((reducedCharacter59 eta)⁻¹ sigma : (ZMod 59)ˣ) : ZMod 59) *
      supportValuationAt
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (S := placesOver827 K) selected y.1
  simp [eta, reducedCharacter59_apply, mul_comm, mul_assoc]

end Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827
