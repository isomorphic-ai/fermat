/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Complex conjugation in the explicit 827 place orbit

This file identifies the conjugate prime used by the sparse 827 source with
the `-1` coordinate of the canonical cyclotomic place action.  The equality
is proved on the integral power-basis generator: both automorphisms send the
canonical primitive 59th root to its inverse.

No place permutation or Fourier phase is supplied as data.
-/
import Fermat.FiftyNine.Conservation.ConjugatePairSource827
import Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827

open scoped NumberField Pointwise

noncomputable section

namespace Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827

open Fermat.FiftyNine.Conservation.ConjugatePairSource827
open Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

private abbrev canonicalZeta59 (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K] : K :=
  IsCyclotomicExtension.zeta 59 ℚ K

private abbrev canonicalZeta59_isPrimitive
    (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K] :
    IsPrimitiveRoot (canonicalZeta59 K) 59 :=
  IsCyclotomicExtension.zeta_spec 59 ℚ K

/-- Mathlib's CM conjugation sends the canonical primitive 59th root to its
inverse.  The proof uses the intrinsic torsion-unit characterization, not a
historical cyclotomic import. -/
private theorem complexConj_canonicalZeta59 :
    NumberField.IsCMField.complexConj K (canonicalZeta59 K) =
      (canonicalZeta59 K)⁻¹ := by
  let hZeta := canonicalZeta59_isPrimitive K
  let rootUnit : (NumberField.RingOfIntegers K)ˣ :=
    (hZeta.toInteger_isPrimitiveRoot.isUnit (by norm_num)).unit
  have hpow : rootUnit ^ 59 = 1 := by
    apply Units.ext
    apply NumberField.RingOfIntegers.ext
    simpa [rootUnit] using hZeta.pow_eq_one
  have ht : rootUnit ∈ NumberField.Units.torsion K := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    exact ⟨59, by norm_num, hpow⟩
  have hc := NumberField.IsCMField.unitsComplexConj_torsion K ⟨rootUnit, ht⟩
  have hc' : NumberField.IsCMField.unitsComplexConj K rootUnit =
      rootUnit⁻¹ := by
    simpa using hc
  have hv := congrArg Units.val hc'
  simpa [rootUnit, NumberField.IsCMField.unitsComplexConj,
    NumberField.IsCMField.ringOfIntegersComplexConj,
    NumberField.RingOfIntegers.ext_iff] using
      congrArg ((↑) : NumberField.RingOfIntegers K → K) hv

private theorem canonicalZeta59_pow_fiftyEight :
    canonicalZeta59 K ^ 58 = (canonicalZeta59 K)⁻¹ := by
  let hZeta := canonicalZeta59_isPrimitive K
  have hne : canonicalZeta59 K ≠ 0 := hZeta.ne_zero (by norm_num)
  apply mul_left_cancel₀ hne
  rw [← pow_succ', show 58 + 1 = 59 by norm_num,
    hZeta.pow_eq_one, mul_inv_cancel₀ hne]

/-- On the ring of integers, CM conjugation is exactly the cyclotomic
automorphism indexed by `-1` in `(ZMod 59)ˣ`. -/
theorem ringOfIntegersComplexConj_eq_cyclotomic_negOne59 :
    (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv =
      KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := 59) K (-1 : GaloisIndex59) := by
  let hZeta := canonicalZeta59_isPrimitive K
  let conjugation : NumberField.RingOfIntegers K →ₐ[ℤ]
      NumberField.RingOfIntegers K :=
    (NumberField.IsCMField.ringOfIntegersComplexConj K).restrictScalars ℤ
  let minusOne : NumberField.RingOfIntegers K →ₐ[ℤ]
      NumberField.RingOfIntegers K :=
    (KummerCriterion.cyclotomicRingOfIntegersEquiv
      (p := 59) K (-1 : GaloisIndex59)).toRingHom.toIntAlgHom
  have heq : conjugation = minusOne := by
    apply hZeta.integralPowerBasis.algHom_ext
    rw [hZeta.integralPowerBasis_gen]
    apply NumberField.RingOfIntegers.ext
    dsimp [conjugation, minusOne]
    change NumberField.IsCMField.complexConj K (canonicalZeta59 K) =
      KummerCriterion.cyclotomicSigmaOfUnit
        (p := 59) K (-1 : GaloisIndex59) (canonicalZeta59 K)
    rw [complexConj_canonicalZeta59,
      KummerCriterion.cyclotomicSigmaOfUnit_apply_zeta]
    rw [show ((-1 : GaloisIndex59) : ZMod 59).val = 58 by decide]
    exact canonicalZeta59_pow_fiftyEight.symm
  apply RingEquiv.ext
  intro x
  change conjugation x = minusOne x
  exact DFunLike.congr_fun heq x

/-- Equality of the underlying height-one places: conjugating an 827 prime
is the `-1` cyclotomic translate of that prime. -/
theorem cmConjugatePlace827_val_eq_cyclotomic_negOne
    (place : Place827 K) :
    (cmConjugatePlace827 place).1 =
      cyclotomicPlaceEquiv59 K (-1 : GaloisIndex59) place.1 := by
  apply IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
  change Ideal.map
      (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom
        place.1.asIdeal =
    Ideal.comap
      (KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := 59) K (-1 : GaloisIndex59)).symm.toRingHom place.1.asIdeal
  rw [ringOfIntegersComplexConj_eq_cyclotomic_negOne59]
  exact Ideal.map_comap_of_equiv
    (KummerCriterion.cyclotomicRingOfIntegersEquiv
      (p := 59) K (-1 : GaloisIndex59))

/-- Bundled equality inside the actual subtype of all places over 827. -/
theorem cmConjugatePlace827_eq_cyclotomic_negOne
    (place : Place827 K) :
    cmConjugatePlace827 place =
      ⟨cyclotomicPlaceEquiv59 K (-1 : GaloisIndex59) place.1,
        (cyclotomicPlaceEquiv59_mem_placesOver827_iff
          K (-1 : GaloisIndex59) place.1).mpr place.2⟩ := by
  apply Subtype.ext
  exact cmConjugatePlace827_val_eq_cyclotomic_negOne place

/-- In the repository's regular orbit coordinates, the conjugate place is
literally the entry indexed by `-1`. -/
theorem cmConjugatePlace827_eq_indexedPlaceOrbit_negOne
    (place : Place827 K) :
    cmConjugatePlace827 place =
      indexedPlaceOrbitEquiv827 K place (-1 : GaloisIndex59) := by
  apply Subtype.ext
  rw [cmConjugatePlace827_val_eq_cyclotomic_negOne,
    indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59]

/-- Since the 827-place orbit is regular and `-1 ≠ 1` modulo 59, no
place in that orbit is fixed by complex conjugation. -/
theorem cmConjugatePlace827_ne_self (place : Place827 K) :
    cmConjugatePlace827 place ≠ place := by
  rw [cmConjugatePlace827_eq_indexedPlaceOrbit_negOne]
  intro h
  have hone : indexedPlaceOrbitEquiv827 K place (1 : GaloisIndex59) =
      place := by
    apply Subtype.ext
    rw [indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59]
    apply IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
    change Ideal.comap
      (KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := 59) K (1 : GaloisIndex59)).symm.toRingHom place.1.asIdeal =
      place.1.asIdeal
    rw [show KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := 59) K (1 : GaloisIndex59) = RingEquiv.refl _ by
      apply RingEquiv.ext
      intro x
      exact KummerCriterion.cyclotomicRingOfIntegersEquiv_one_apply
        (p := 59) K x]
    simp
  have hindex : (-1 : GaloisIndex59) = 1 := by
    apply (indexedPlaceOrbitEquiv827 K place).injective
    exact h.trans hone.symm
  have hval := congrArg (fun sigma : GaloisIndex59 ↦ (sigma : ZMod 59)) hindex
  exact (by decide : (-1 : ZMod 59) ≠ 1) hval

end Fermat.FiftyNine.Conservation.ConjugatePlaceOrbit827
