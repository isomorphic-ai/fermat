/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The canonical reflected projection of the conjugate-pair source

The sparse divisor `P * conjugate(P)` has localization support in exactly
the `1` and `-1` positions of the regular 827-place orbit.  This file expands
the genuine character idempotent through Mathlib's supported valuation and
computes its canonical reflected `(59, 44)` coordinate:

`reduction(1 / 58) * (-2)`.

Both factors are nonzero modulo 59.  Thus the honest q-relaxed source built
from the conjugation-fixed ideal has a nonzero canonical reflected
localization.  No projected-mode certificate or localization functional is
supplied as data.
-/
import Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
import Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827

open scoped MonoidAlgebra nonZeroDivisors NumberField Pointwise

noncomputable section

namespace Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827
open Fermat.FiftyNine.Conservation.ConjugatePairSource827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : DecidableEq
    (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :=
  Classical.decEq _

/-- Every raw localization coordinate is the negative coordinate of the
conjugate-pair ideal. -/
theorem supportValuationAt_conjugatePairSource827_eq
    (place target : Place827 K) :
    supportValuationAt
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (S := placesOver827 K) target
        (conjugatePairSource827 place) =
      -(FractionalIdeal.count K target.1
        (conjugatePairIdeal827 place :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) : ZMod 59) := by
  change ((target.1.valuationOfNeZero
    (conjugatePairUnit827 place)).toAdd : ZMod 59) = _
  exact conjugatePairUnit827_valuation_mod place target.1

/-- Supported localization is contragredient under the canonical cyclotomic
action, before applying any character projector. -/
theorem supportValuationAt_cyclotomic_apply
    (sigma : GaloisIndex59) (source : QRelaxedSelmerCarrier827 K)
    (target : Place827 K) :
    supportValuationAt
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (S := placesOver827 K) target
        ((cyclotomicQRelaxedSelmerRepresentation827 K) sigma source) =
      supportValuationAt
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (S := placesOver827 K)
        ⟨cyclotomicPlaceEquiv59 K sigma⁻¹ target.1,
          (cyclotomicPlaceEquiv59_mem_placesOver827_iff
            K sigma⁻¹ target.1).mpr target.2⟩ source := by
  change Multiplicative.toAdd
      (target.1.valuationOfNeZeroMod 59
        (cyclotomicKummerHom59 K sigma (Additive.toMul source).1)) =
    Multiplicative.toAdd
      ((cyclotomicPlaceEquiv59 K sigma⁻¹ target.1).valuationOfNeZeroMod 59
        (Additive.toMul source).1)
  exact congrArg Multiplicative.toAdd
    (cyclotomicValuationCovariance59 K sigma target.1
      (Additive.toMul source).1)

/-- Regularity of the 827 orbit, expressed as the stabilizer of a selected
place being trivial. -/
theorem cyclotomicPlaceEquiv59_eq_self_iff
    (selected : Place827 K) (sigma : GaloisIndex59) :
    cyclotomicPlaceEquiv59 K sigma selected.1 = selected.1 ↔ sigma = 1 := by
  have hone : cyclotomicPlaceEquiv59 K 1 selected.1 = selected.1 := by
    apply IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
    change Ideal.comap
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := 59) K 1).symm.toRingHom selected.1.asIdeal =
      selected.1.asIdeal
    have heq : KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := 59) K 1 = RingEquiv.refl _ := by
      apply RingEquiv.ext
      exact KummerCriterion.cyclotomicRingOfIntegersEquiv_one_apply
        (p := 59) K
    rw [heq]
    simp
  constructor
  · intro h
    let orbit := indexedPlaceOrbitEquiv827 K selected
    apply orbit.injective
    have hsigma : orbit sigma = selected := by
      apply Subtype.ext
      rw [indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59]
      exact h
    have hone' : orbit 1 = selected := by
      apply Subtype.ext
      rw [indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59]
      exact hone
    exact hsigma.trans hone'.symm
  · rintro rfl
    exact hone

/-- The regular cyclotomic orbit map based at any selected 827 place is
injective. -/
theorem cyclotomicPlaceEquiv59_injective_at
    (selected : Place827 K) {sigma tau : GaloisIndex59}
    (h : cyclotomicPlaceEquiv59 K sigma selected.1 =
      cyclotomicPlaceEquiv59 K tau selected.1) : sigma = tau := by
  let orbit := indexedPlaceOrbitEquiv827 K selected
  apply orbit.injective
  apply Subtype.ext
  rw [indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59,
    indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59]
  exact h

/-- In the unprojected orbit sum, the conjugate-pair source has coefficient
`-1` exactly at positions `1` and `-1`, and zero elsewhere. -/
theorem conjugatePairSource827_orbit_coordinate
    (place : Place827 K) (sigma : GaloisIndex59)
    (hcm : (cmConjugatePlace827 place).1 =
      cyclotomicPlaceEquiv59 K (-1) place.1) :
    supportValuationAt
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (S := placesOver827 K) place
        ((cyclotomicQRelaxedSelmerRepresentation827 K) sigma
          (conjugatePairSource827 place)) =
      if sigma = 1 then -1
      else if sigma = (-1 : GaloisIndex59) then -1 else 0 := by
  rw [supportValuationAt_cyclotomic_apply,
    supportValuationAt_conjugatePairSource827_eq,
    conjugatePairIdeal827_count]
  have hfirst : place.1 =
      cyclotomicPlaceEquiv59 K sigma⁻¹ place.1 ↔ sigma = 1 := by
    rw [eq_comm, cyclotomicPlaceEquiv59_eq_self_iff]
    simp
  have hsecond : (cmConjugatePlace827 place).1 =
      cyclotomicPlaceEquiv59 K sigma⁻¹ place.1 ↔
        sigma = (-1 : GaloisIndex59) := by
    rw [hcm]
    constructor
    · intro h
      have hindex : (-1 : GaloisIndex59) = sigma⁻¹ :=
        cyclotomicPlaceEquiv59_injective_at place h
      have hinv := congrArg Inv.inv hindex
      simpa using hinv.symm
    · rintro rfl
      simp
  rw [if_congr hfirst rfl rfl, if_congr hsecond rfl rfl]
  have hne : (1 : GaloisIndex59) ≠ -1 := by decide
  have hne' : (-1 : GaloisIndex59) ≠ 1 := Ne.symm hne
  by_cases h1 : sigma = 1
  · simp [h1, hne]
  · by_cases hm1 : sigma = (-1 : GaloisIndex59)
    · simp [hm1, hne']
    · simp [h1, hm1]

/-- The inverse-character-weighted orbit sum of the sparse source consists
of just its identity and conjugation coefficients. -/
theorem conjugatePairSource827_weighted_sum
    (eta : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (place : Place827 K)
    (hcm : (cmConjugatePlace827 place).1 =
      cyclotomicPlaceEquiv59 K (-1) place.1) :
    (∑ sigma : GaloisIndex59,
      PadicInt.toZMod (↑((eta sigma)⁻¹) : PadicInt 59) *
        supportValuationAt
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (S := placesOver827 K) place
          ((cyclotomicQRelaxedSelmerRepresentation827 K) sigma
            (conjugatePairSource827 place))) =
      -PadicInt.toZMod (↑((eta 1)⁻¹) : PadicInt 59) +
        -PadicInt.toZMod (↑((eta (-1))⁻¹) : PadicInt 59) := by
  classical
  simp_rw [conjugatePairSource827_orbit_coordinate place _ hcm]
  have hne : (1 : GaloisIndex59) ≠ -1 := by decide
  have hsummand (sigma : GaloisIndex59) :
      PadicInt.toZMod (↑((eta sigma)⁻¹) : PadicInt 59) *
          (if sigma = 1 then -1
            else if sigma = (-1 : GaloisIndex59) then -1 else 0) =
        (if sigma = 1 then
          -PadicInt.toZMod (↑((eta 1)⁻¹) : PadicInt 59) else 0) +
        (if sigma = (-1 : GaloisIndex59) then
          -PadicInt.toZMod (↑((eta (-1))⁻¹) : PadicInt 59) else 0) := by
    by_cases h1 : sigma = 1
    · subst sigma
      simp [hne]
    · by_cases hm1 : sigma = (-1 : GaloisIndex59)
      · subst sigma
        simp [Ne.symm hne]
      · simp [h1, hm1]
  simp_rw [hsummand]
  rw [Finset.sum_add_distrib]
  simp

private abbrev canonicalReflectedCharacter59 :
    InvolutiveBase.Character (PadicInt 59) GaloisIndex59 :=
  InvolutiveBase.reflectedCharacter
    canonicalTeichmullerCharacter59 irregularCharacter59

private theorem canonical_reflected_coefficient_one :
    PadicInt.toZMod
        (↑((canonicalReflectedCharacter59 1)⁻¹) : PadicInt 59) = 1 := by
  simp [canonicalReflectedCharacter59]

private theorem canonical_reflected_coefficient_neg_one :
    PadicInt.toZMod
        (↑((canonicalReflectedCharacter59 (-1))⁻¹) : PadicInt 59) = 1 := by
  have heven := orientedPrimalMode827_canonical_irregular_even
  have hval := congrArg Units.val heven
  change PadicInt.toZMod
      (canonicalReflectedCharacter59 (-1) : PadicInt 59) = 1 at hval
  have hprod := congrArg PadicInt.toZMod
    (canonicalReflectedCharacter59 (-1)).inv_val
  simp only [map_mul, map_one] at hprod
  rw [hval, mul_one] at hprod
  exact hprod

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- Applying a genuine character idempotent and then reading one supported
valuation coordinate is the normalized inverse-character-weighted orbit
sum. -/
theorem supportValuationAt_characterProjectorAt_eq_sum
    (eta : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (source : QRelaxedSelmerCarrier827 K) (target : Place827 K) :
    supportValuationAt
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (S := placesOver827 K) target
        ((SelmerEigenspace.characterProjectorAt
          (cyclotomicQRelaxedSelmerRepresentation827 K) eta source).1) =
      PadicInt.toZMod
          (⅟(Fintype.card GaloisIndex59 : PadicInt 59)) *
        ∑ sigma : GaloisIndex59,
          PadicInt.toZMod (↑((eta sigma)⁻¹) : PadicInt 59) *
            supportValuationAt
              (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
              (S := placesOver827 K) target
              ((cyclotomicQRelaxedSelmerRepresentation827 K) sigma source) := by
  change supportValuationAt
      (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
      (S := placesOver827 K) target
      ((cyclotomicQRelaxedSelmerRepresentation827 K).asAlgebraHom
        (InvolutiveBase.characterIdempotent eta) source) = _
  rw [InvolutiveBase.characterIdempotent, map_smul, map_sum]
  simp only [LinearMap.smul_apply,
    Representation.asAlgebraHom_single]
  rw [SelmerEigenspace.padicInt_smul_eq_toZMod_smul]
  have hout := ZMod.map_smul
    (supportValuationAt
      (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
      (S := placesOver827 K) target)
    (PadicInt.toZMod
      (⅟(Fintype.card GaloisIndex59 : PadicInt 59)))
    ((∑ x : GaloisIndex59,
      (↑((eta x)⁻¹) : PadicInt 59) •
        (cyclotomicQRelaxedSelmerRepresentation827 K) x) source)
  rw [hout]
  rw [LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smul_apply]
  simp_rw [SelmerEigenspace.padicInt_smul_eq_toZMod_smul]
  apply congrArg
    (fun z : ZMod 59 =>
      PadicInt.toZMod
        (⅟(Fintype.card GaloisIndex59 : PadicInt 59)) * z)
  apply Finset.sum_congr rfl
  intro sigma _
  rw [ZMod.map_smul
    (supportValuationAt
      (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
      (S := placesOver827 K) target)
    (PadicInt.toZMod (↑((eta sigma)⁻¹) : PadicInt 59))
    ((cyclotomicQRelaxedSelmerRepresentation827 K) sigma source)]
  rfl

/-- The selected localization of the canonical reflected projection is
exactly the normalized scalar `-2/58`. -/
theorem canonical_projected_conjugatePair_coordinate_eq
    (place : Place827 K) :
    qLocalizationCoordinate827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59 place
        (qRelaxedReflectedProjector827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (conjugatePairSource827 place)) =
      PadicInt.toZMod
          (⅟(Fintype.card GaloisIndex59 : PadicInt 59)) * (-2) := by
  change supportValuationAt
      (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
      (S := placesOver827 K) place
      ((SelmerEigenspace.characterProjectorAt
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalReflectedCharacter59
        (conjugatePairSource827 place)).1) = _
  rw [supportValuationAt_characterProjectorAt_eq_sum]
  rw [conjugatePairSource827_weighted_sum canonicalReflectedCharacter59 place
    (cmConjugatePlace827_val_eq_cyclotomic_negOne place)]
  rw [canonical_reflected_coefficient_one,
    canonical_reflected_coefficient_neg_one]
  ring

/-- The reduction of the normalized group-order inverse cannot vanish. -/
theorem projectedNormalization59_ne_zero :
    PadicInt.toZMod
        (⅟(Fintype.card GaloisIndex59 : PadicInt 59)) ≠ 0 := by
  intro hzero
  have hmul := congrArg PadicInt.toZMod
    (invOf_mul_self
      (Fintype.card GaloisIndex59 : PadicInt 59))
  simp only [map_mul, map_one] at hmul
  rw [hzero, zero_mul] at hmul
  exact zero_ne_one hmul

/-- The honest conjugate-pair q-relaxed source survives the canonical
reflected `(59, 44)` projector with nonzero selected localization. -/
theorem canonical_projected_conjugatePair_coordinate_ne_zero
    (place : Place827 K) :
    qLocalizationCoordinate827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59 place
        (qRelaxedReflectedProjector827
          (cyclotomicQRelaxedSelmerRepresentation827 K)
          canonicalTeichmullerCharacter59 irregularCharacter59
          (conjugatePairSource827 place)) ≠ 0 := by
  rw [canonical_projected_conjugatePair_coordinate_eq]
  exact mul_ne_zero projectedNormalization59_ne_zero
    (by decide : (-2 : ZMod 59) ≠ 0)

end Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827
