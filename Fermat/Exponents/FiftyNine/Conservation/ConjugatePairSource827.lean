/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# A conjugate-pair q-relaxed source at 827

For one actual place `P` above 827, the integral ideal

`P * conjugate(P)`

is fixed by complex conjugation and supported entirely above 827.  The
maximal-real class-number certificate therefore gives a principal equation
whose field-unit generator has the negative of this two-point divisor modulo
59.  This file seats that generator in Mathlib's literal 827-relaxed Selmer
carrier and proves its raw supported localization is nonzero.

The reflected-character projector is deliberately not evaluated here.  Its
even Fourier component is the next, separate step.
-/
import Fermat.Exponents.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59
import Fermat.Exponents.FiftyNine.Conservation.CyclotomicSelmerAction59

open scoped nonZeroDivisors NumberField Pointwise WithZero

noncomputable section

namespace Fermat.FiftyNine.Conservation.ConjugatePairSource827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : DecidableEq
    (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :=
  Classical.decEq _

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

local notation3 "K⁺" => NumberField.maximalRealSubfield K

private theorem plusClassGroup_card_coprime_fiftyNine :
    Nat.Coprime (Nat.card (ClassGroup (NumberField.RingOfIntegers K⁺))) 59 := by
  rw [Nat.card_eq_fintype_card]
  apply Nat.Coprime.symm
  exact (by norm_num : Nat.Prime 59).coprime_iff_not_dvd.mpr
    (Fermat.FiftyNine.Conservation.Fold.not_dvd_plusClassNumber (K := K))

/-- Complex-conjugate transport of an integral ideal. -/
noncomputable def cmConjugateIdeal827
    (I : Ideal (NumberField.RingOfIntegers K)) :
    Ideal (NumberField.RingOfIntegers K) :=
  I.map
    (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom

/-- Complex conjugation is involutive on integral ideals. -/
@[simp]
theorem cmConjugateIdeal827_involutive
    (I : Ideal (NumberField.RingOfIntegers K)) :
    cmConjugateIdeal827 (cmConjugateIdeal827 I) = I := by
  unfold cmConjugateIdeal827
  rw [Ideal.map_map]
  have hc :
      (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom.comp
          (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
        RingHom.id (NumberField.RingOfIntegers K) := by
    ext x
    exact NumberField.IsCMField.complexConj_apply_apply K x
  rw [hc, Ideal.map_id]

/-- Conjugation preserves the rational prime below an integral ideal. -/
theorem cmConjugateIdeal827_under_int
    (I : Ideal (NumberField.RingOfIntegers K)) :
    (cmConjugateIdeal827 I).under ℤ = I.under ℤ := by
  unfold cmConjugateIdeal827
  ext z
  simp only [Ideal.mem_under]
  rw [show I.map
      (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      I.comap
        (NumberField.IsCMField.ringOfIntegersComplexConj K).symm.toRingEquiv.toRingHom by
    exact Ideal.map_comap_of_equiv
      (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv]
  change (NumberField.IsCMField.ringOfIntegersComplexConj K).symm
      (algebraMap ℤ (NumberField.RingOfIntegers K) z) ∈ I ↔
    algebraMap ℤ (NumberField.RingOfIntegers K) z ∈ I
  rw [show (NumberField.IsCMField.ringOfIntegersComplexConj K).symm
      (algebraMap ℤ (NumberField.RingOfIntegers K) z) =
        algebraMap ℤ (NumberField.RingOfIntegers K) z by
    exact
      (NumberField.IsCMField.ringOfIntegersComplexConj K).symm.commutes z]

/-- The conjugate of an actual 827 place, retained as an actual 827 place. -/
noncomputable def cmConjugatePlace827 (place : Place827 K) : Place827 K := by
  let conjugatePlace : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K) :=
    { asIdeal := cmConjugateIdeal827 place.1.asIdeal
      isPrime := by
        letI : place.1.asIdeal.IsPrime := place.1.isPrime
        exact Ideal.map_isPrime_of_equiv
          (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv
      ne_bot := by
        apply (Ideal.map_eq_bot_iff_of_injective
          (NumberField.IsCMField.ringOfIntegersComplexConj K).injective).not.mpr
        exact place.1.ne_bot }
  exact ⟨conjugatePlace, by
    change rationalPrimeIdeal827 = conjugatePlace.asIdeal.under ℤ
    rw [show conjugatePlace.asIdeal =
      cmConjugateIdeal827 place.1.asIdeal from rfl,
      cmConjugateIdeal827_under_int]
    exact place.2⟩

@[simp]
theorem cmConjugatePlace827_asIdeal (place : Place827 K) :
    (cmConjugatePlace827 place).1.asIdeal =
      cmConjugateIdeal827 place.1.asIdeal :=
  rfl

/-- The sparse even divisor consisting of one 827 prime and its complex
conjugate. -/
noncomputable def conjugatePairIdeal827 (place : Place827 K) :
    Ideal (NumberField.RingOfIntegers K) :=
  place.1.asIdeal * cmConjugateIdeal827 place.1.asIdeal

theorem conjugatePairIdeal827_ne_zero (place : Place827 K) :
    conjugatePairIdeal827 place ≠ 0 := by
  apply mul_ne_zero place.1.ne_bot
  apply (Ideal.map_eq_bot_iff_of_injective
    (NumberField.IsCMField.ringOfIntegersComplexConj K).injective).not.mpr
  exact place.1.ne_bot

/-- The two-point 827 divisor is genuinely fixed by complex conjugation. -/
theorem conjugatePairIdeal827_fixed (place : Place827 K) :
    (conjugatePairIdeal827 place).map
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      conjugatePairIdeal827 place := by
  unfold conjugatePairIdeal827 cmConjugateIdeal827
  rw [Ideal.map_mul, Ideal.map_map]
  have hc :
      (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom.comp
          (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
        RingHom.id (NumberField.RingOfIntegers K) := by
    ext x
    exact NumberField.IsCMField.complexConj_apply_apply K x
  rw [hc, Ideal.map_id, mul_comm]

/-- Exact factorization coordinates of the two-point divisor. -/
theorem conjugatePairIdeal827_count
    (place : Place827 K)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    FractionalIdeal.count K v
        (conjugatePairIdeal827 place :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
      (if place.1 = v then 1 else 0) +
        (if (cmConjugatePlace827 place).1 = v then 1 else 0) := by
  classical
  rw [conjugatePairIdeal827, FractionalIdeal.coeIdeal_mul]
  rw [← cmConjugatePlace827_asIdeal place]
  rw [FractionalIdeal.count_mul K v
    (FractionalIdeal.coeIdeal_ne_zero.mpr place.1.ne_bot)
    (FractionalIdeal.coeIdeal_ne_zero.mpr
      (cmConjugatePlace827 place).1.ne_bot)]
  rw [FractionalIdeal.count_maximal K v place.1,
    FractionalIdeal.count_maximal K v (cmConjugatePlace827 place).1]

/-- Away from the complete 827 support, the conjugate-pair ideal has no
factorization coordinate. -/
theorem conjugatePairIdeal827_count_eq_zero_of_not_mem
    (place : Place827 K)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) (hv : v ∉ placesOver827 K) :
    FractionalIdeal.count K v
        (conjugatePairIdeal827 place :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) = 0 := by
  rw [conjugatePairIdeal827_count]
  have hplace : place.1 ≠ v := by
    intro h
    exact hv (h ▸ place.2)
  have hconjugate : (cmConjugatePlace827 place).1 ≠ v := by
    intro h
    exact hv (h ▸ (cmConjugatePlace827 place).2)
  simp [hplace, hconjugate]

/-- The selected coordinate of the sparse divisor is either `-1` or `-2`
modulo 59, and is therefore nonzero without needing to distinguish whether
the selected prime is fixed by conjugation. -/
theorem neg_conjugatePairIdeal827_count_selected_ne_zero
    (place : Place827 K) :
    -(FractionalIdeal.count K place.1
        (conjugatePairIdeal827 place :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) : ZMod 59) ≠ 0 := by
  classical
  rw [conjugatePairIdeal827_count]
  by_cases hconjugate : (cmConjugatePlace827 place).1 = place.1
  · simp [hconjugate]
    exact (by decide : (2 : ZMod 59) ≠ 0)
  · simp [hconjugate]

/-! ## Retaining the plus-class provenance -/

/-- Strong principal data retaining the maximal-real provenance of the
chosen 59th-root ideal.  This extra receipt is load-bearing: the valuation
congruence by itself does not distinguish roots differing by 59-torsion. -/
theorem exists_plus_principal_data827
    (place : Place827 K) :
    ∃ (realRoot : ClassGroup (NumberField.RingOfIntegers K⁺))
      (J : (Ideal (NumberField.RingOfIntegers K))⁰) (x : Kˣ),
      let extendedRoot : ClassGroup (NumberField.RingOfIntegers K) :=
        ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
          (NumberField.RingOfIntegers K) realRoot
      let idealClass : ClassGroup (NumberField.RingOfIntegers K) :=
        ClassGroup.mk0 ⟨conjugatePairIdeal827 place,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            (conjugatePairIdeal827_ne_zero place)⟩
      ClassGroup.mk0 J = extendedRoot ^ 30 * idealClass⁻¹ ∧
      extendedRoot ^ 59 = idealClass ^ 2 ∧
      FractionalIdeal.spanSingleton
          (NumberField.RingOfIntegers K)⁰ (x : K) *
        ((J : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ 59 =
        (conjugatePairIdeal827 place :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) := by
  let I := conjugatePairIdeal827 place
  have hI : I ≠ 0 := conjugatePairIdeal827_ne_zero place
  let N : Ideal (NumberField.RingOfIntegers K⁺) :=
    Ideal.relNorm (NumberField.RingOfIntegers K⁺) I
  have hN : N ≠ 0 := by
    intro hzero
    apply hI
    exact Ideal.relNorm_eq_bot_iff.mp hzero
  let normClass : ClassGroup (NumberField.RingOfIntegers K⁺) :=
    ClassGroup.mk0 ⟨N, mem_nonZeroDivisors_iff_ne_zero.mpr hN⟩
  obtain ⟨realRoot, hrealRoot⟩ :=
    (plusClassGroup_card_coprime_fiftyNine (K := K)).pow_left_bijective.2
      normClass
  change realRoot ^ 59 = normClass at hrealRoot
  let extendedRoot : ClassGroup (NumberField.RingOfIntegers K) :=
    ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
      (NumberField.RingOfIntegers K) realRoot
  let idealClass : ClassGroup (NumberField.RingOfIntegers K) :=
    ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  have hfixed :
      I.map (NumberField.IsCMField.ringOfIntegersComplexConj K) = I := by
    exact conjugatePairIdeal827_fixed place
  have hnormMap :
      Ideal.map (algebraMap (NumberField.RingOfIntegers K⁺)
        (NumberField.RingOfIntegers K)) N = I ^ 2 := by
    change Ideal.map (algebraMap (NumberField.RingOfIntegers K⁺)
        (NumberField.RingOfIntegers K))
        (Ideal.relNorm (NumberField.RingOfIntegers K⁺) I) = I ^ 2
    rw [Fermat.Conservation.Credit.Fold.map_relativeNorm_eq_mul_conjugate I hI,
      hfixed, pow_two]
  have hextendedRoot : extendedRoot ^ 59 = idealClass ^ 2 := by
    calc
      extendedRoot ^ 59 =
          ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
            (NumberField.RingOfIntegers K) (realRoot ^ 59) := by rw [map_pow]
      _ = ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
          (NumberField.RingOfIntegers K) normClass := by rw [hrealRoot]
      _ = ClassGroup.mk0
          (ClassGroup.extendedIdeal (NumberField.RingOfIntegers K⁺)
            (NumberField.RingOfIntegers K)
            ⟨N, mem_nonZeroDivisors_iff_ne_zero.mpr hN⟩) := by
            exact ClassGroup.extendedHom_mk0
              (NumberField.RingOfIntegers K⁺) (NumberField.RingOfIntegers K) _
      _ = idealClass ^ 2 := by
            rw [← map_pow]
            congr 1
            apply Subtype.ext
            exact hnormMap
  let rootClass := extendedRoot ^ 30 * idealClass⁻¹
  have hrootClass : rootClass ^ 59 = idealClass := by
    rw [mul_pow, inv_pow]
    calc
      (extendedRoot ^ 30) ^ 59 * (idealClass ^ 59)⁻¹ =
          (extendedRoot ^ 59) ^ 30 * (idealClass ^ 59)⁻¹ := by
            congr 1
            rw [← pow_mul, show 30 * 59 = 59 * 30 by norm_num, pow_mul]
      _ = (idealClass ^ 2) ^ 30 * (idealClass ^ 59)⁻¹ := by
            rw [hextendedRoot]
      _ = idealClass := by group
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective rootClass
  let I₀ : (Ideal (NumberField.RingOfIntegers K))⁰ :=
    ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  have hclasses : ClassGroup.mk0 (J ^ 59) = ClassGroup.mk0 I₀ := by
    rw [map_pow, hJ]
    exact hrootClass
  obtain ⟨x, hx, hprincipal⟩ :=
    (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring (K := K)).mp hclasses
  let xu : Kˣ := Units.mk0 x hx
  refine ⟨realRoot, J, xu, hJ, hextendedRoot, ?_⟩
  have hJpow :
      (((J ^ 59 : (Ideal (NumberField.RingOfIntegers K))⁰) :
          Ideal (NumberField.RingOfIntegers K)) :
        FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
      ((J : Ideal (NumberField.RingOfIntegers K)) :
        FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ 59 := by
    exact FractionalIdeal.coeIdeal_pow
      (S := (NumberField.RingOfIntegers K)⁰) (P := K) J 59
  rw [← hJpow]
  simpa only [xu, Units.val_mk0, FractionalIdeal.coe_mk0, I₀, I]
    using hprincipal

/-- The conjugate-pair ideal itself vanishes in the 827 class quotient. -/
theorem conjugatePairIdeal827_class_eq_one
    (place : Place827 K) :
    IsDedekindDomain.selmerGroup.classGroupToObstructionTarget
        (R := NumberField.RingOfIntegers K) (K := K) (placesOver827 K)
        (ClassGroup.mk0
          ⟨conjugatePairIdeal827 place,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              (conjugatePairIdeal827_ne_zero place)⟩) = 1 := by
  let P0 : (Ideal (NumberField.RingOfIntegers K))⁰ :=
    ⟨place.1.asIdeal,
      mem_nonZeroDivisors_iff_ne_zero.mpr place.1.ne_bot⟩
  let Pc : (Ideal (NumberField.RingOfIntegers K))⁰ :=
    ⟨(cmConjugatePlace827 place).1.asIdeal,
      mem_nonZeroDivisors_iff_ne_zero.mpr
        (cmConjugatePlace827 place).1.ne_bot⟩
  have hpair :
      (⟨conjugatePairIdeal827 place,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          (conjugatePairIdeal827_ne_zero place)⟩ :
        (Ideal (NumberField.RingOfIntegers K))⁰) = P0 * Pc := by
    apply Subtype.ext
    change conjugatePairIdeal827 place =
      place.1.asIdeal * (cmConjugatePlace827 place).1.asIdeal
    rw [conjugatePairIdeal827, cmConjugatePlace827_asIdeal]
  rw [hpair, map_mul]
  have hP0 : ClassGroup.mk0 P0 =
      IsDedekindDomain.selmerGroup.primeClass place.1 := rfl
  have hPc : ClassGroup.mk0 Pc =
      IsDedekindDomain.selmerGroup.primeClass
        (cmConjugatePlace827 place).1 := rfl
  rw [hP0, hPc, map_mul,
    IsDedekindDomain.selmerGroup.classGroupToObstructionTarget_primeClass
      (R := NumberField.RingOfIntegers K) (K := K) (placesOver827 K) place,
    IsDedekindDomain.selmerGroup.classGroupToObstructionTarget_primeClass
      (R := NumberField.RingOfIntegers K) (K := K) (placesOver827 K)
        (cmConjugatePlace827 place), one_mul]

/-- A real-fold class whose 59th power is the conjugate pair dies after
discarding the 827 places: its image is killed by both 59 and the plus class
number, and those exponents are coprime. -/
theorem extendedRealRoot827_class_eq_one
    (place : Place827 K)
    (realRoot : ClassGroup (NumberField.RingOfIntegers K⁺))
    (hextended :
      (ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
          (NumberField.RingOfIntegers K) realRoot) ^ 59 =
        (ClassGroup.mk0
          ⟨conjugatePairIdeal827 place,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              (conjugatePairIdeal827_ne_zero place)⟩) ^ 2) :
    IsDedekindDomain.selmerGroup.classGroupToObstructionTarget
        (R := NumberField.RingOfIntegers K) (K := K) (placesOver827 K)
        (ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
          (NumberField.RingOfIntegers K) realRoot) = 1 := by
  let f := IsDedekindDomain.selmerGroup.classGroupToObstructionTarget
    (R := NumberField.RingOfIntegers K) (K := K) (placesOver827 K)
  let e := ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
    (NumberField.RingOfIntegers K)
  have hp : (f (e realRoot)) ^ 59 = 1 := by
    rw [← map_pow, hextended, map_pow,
      conjugatePairIdeal827_class_eq_one place, one_pow]
  have hcard :
      (f (e realRoot)) ^
          Fintype.card (ClassGroup (NumberField.RingOfIntegers K⁺)) = 1 := by
    rw [← map_pow, ← map_pow, pow_card_eq_one, map_one, map_one]
  exact (pow_eq_one_iff_of_coprime
    (show Nat.Coprime
        (Fintype.card (ClassGroup (NumberField.RingOfIntegers K⁺))) 59 by
      simpa [Nat.card_eq_fintype_card] using
        (plusClassGroup_card_coprime_fiftyNine (K := K)))).mp
      ⟨hcard, hp⟩

private theorem plusRootIdeal827_class_eq_one
    (place : Place827 K)
    (realRoot : ClassGroup (NumberField.RingOfIntegers K⁺))
    (J : (Ideal (NumberField.RingOfIntegers K))⁰)
    (hJ : ClassGroup.mk0 J =
      (ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
          (NumberField.RingOfIntegers K) realRoot) ^ 30 *
        (ClassGroup.mk0
          ⟨conjugatePairIdeal827 place,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              (conjugatePairIdeal827_ne_zero place)⟩)⁻¹)
    (hextended :
      (ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
          (NumberField.RingOfIntegers K) realRoot) ^ 59 =
        (ClassGroup.mk0
          ⟨conjugatePairIdeal827 place,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              (conjugatePairIdeal827_ne_zero place)⟩) ^ 2) :
    IsDedekindDomain.selmerGroup.classGroupToObstructionTarget
        (R := NumberField.RingOfIntegers K) (K := K) (placesOver827 K)
        (ClassGroup.mk0 J) = 1 := by
  rw [hJ, map_mul, map_pow, map_inv,
    extendedRealRoot827_class_eq_one place realRoot hextended,
    conjugatePairIdeal827_class_eq_one place]
  simp

private theorem exists_principalAway_eq_plusRootIdeal827
    (place : Place827 K)
    (realRoot : ClassGroup (NumberField.RingOfIntegers K⁺))
    (J : (Ideal (NumberField.RingOfIntegers K))⁰)
    (hJ : ClassGroup.mk0 J =
      (ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
          (NumberField.RingOfIntegers K) realRoot) ^ 30 *
        (ClassGroup.mk0
          ⟨conjugatePairIdeal827 place,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              (conjugatePairIdeal827_ne_zero place)⟩)⁻¹)
    (hextended :
      (ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
          (NumberField.RingOfIntegers K) realRoot) ^ 59 =
        (ClassGroup.mk0
          ⟨conjugatePairIdeal827 place,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              (conjugatePairIdeal827_ne_zero place)⟩) ^ 2) :
    ∃ y : Kˣ,
      IsDedekindDomain.selmerGroup.principalDivisorAway
          (R := NumberField.RingOfIntegers K) (K := K) (placesOver827 K) y =
        IsDedekindDomain.selmerGroup.fractionalIdealToDivisorAway
          (R := NumberField.RingOfIntegers K) (K := K) (placesOver827 K)
          (FractionalIdeal.mk0 K J) := by
  have hclass := plusRootIdeal827_class_eq_one
    place realRoot J hJ hextended
  rw [← ClassGroup.mk_mk0 (K := K),
    IsDedekindDomain.selmerGroup.classGroupToObstructionTarget_mk] at hclass
  obtain ⟨y, hy⟩ :=
    (QuotientGroup.eq_one_iff
      (IsDedekindDomain.selmerGroup.fractionalIdealToDivisorAway
        (R := NumberField.RingOfIntegers K) (K := K) (placesOver827 K)
        (FractionalIdeal.mk0 K J))).mp hclass
  exact ⟨y, hy⟩

private theorem conjugatePairIdeal827_divisorAway_eq_one
    (place : Place827 K) :
    IsDedekindDomain.selmerGroup.fractionalIdealToDivisorAway
        (R := NumberField.RingOfIntegers K) (K := K) (placesOver827 K)
        (FractionalIdeal.mk0 K
          ⟨conjugatePairIdeal827 place,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              (conjugatePairIdeal827_ne_zero place)⟩) = 1 := by
  apply Multiplicative.toAdd.injective
  apply Finsupp.ext
  intro v
  rw [IsDedekindDomain.selmerGroup.fractionalIdealToDivisorAway_apply,
    FractionalIdeal.coe_mk0]
  exact conjugatePairIdeal827_count_eq_zero_of_not_mem place v.1 v.2

/-- The retained plus-root data yields a literal 827-unit in the same
59th-power Kummer class as its principal generator. -/
theorem exists_sUnit_eq_kummerClass_of_plus_principal_data827
    (place : Place827 K)
    (realRoot : ClassGroup (NumberField.RingOfIntegers K⁺))
    (J : (Ideal (NumberField.RingOfIntegers K))⁰) (x : Kˣ)
    (hJ : ClassGroup.mk0 J =
      (ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
          (NumberField.RingOfIntegers K) realRoot) ^ 30 *
        (ClassGroup.mk0
          ⟨conjugatePairIdeal827 place,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              (conjugatePairIdeal827_ne_zero place)⟩)⁻¹)
    (hextended :
      (ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
          (NumberField.RingOfIntegers K) realRoot) ^ 59 =
        (ClassGroup.mk0
          ⟨conjugatePairIdeal827 place,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              (conjugatePairIdeal827_ne_zero place)⟩) ^ 2)
    (hprincipal :
      FractionalIdeal.spanSingleton
          (NumberField.RingOfIntegers K)⁰ (x : K) *
        ((J : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ 59 =
        (conjugatePairIdeal827 place :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)) :
    ∃ u : (placesOver827 K).unit K,
      (QuotientGroup.mk (u : Kˣ) :
          Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) =
        QuotientGroup.mk x := by
  obtain ⟨y, hy⟩ := exists_principalAway_eq_plusRootIdeal827
    place realRoot J hJ hextended
  let f := IsDedekindDomain.selmerGroup.fractionalIdealToDivisorAway
    (R := NumberField.RingOfIntegers K) (K := K) (placesOver827 K)
  have hprincipalUnits :
      toPrincipalIdeal (NumberField.RingOfIntegers K) K x *
          (FractionalIdeal.mk0 K J) ^ 59 =
        FractionalIdeal.mk0 K
          ⟨conjugatePairIdeal827 place,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              (conjugatePairIdeal827_ne_zero place)⟩ := by
    apply Units.ext
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val,
      coe_toPrincipalIdeal, FractionalIdeal.coe_mk0] using hprincipal
  have hdivisor :
      IsDedekindDomain.selmerGroup.principalDivisorAway
          (R := NumberField.RingOfIntegers K) (K := K) (placesOver827 K) x *
        (IsDedekindDomain.selmerGroup.principalDivisorAway
          (R := NumberField.RingOfIntegers K) (K := K)
          (placesOver827 K) y) ^ 59 = 1 := by
    rw [hy]
    change f (toPrincipalIdeal
        (NumberField.RingOfIntegers K) K x) *
      (f (FractionalIdeal.mk0 K J)) ^ 59 = 1
    rw [← map_pow, ← map_mul, hprincipalUnits,
      conjugatePairIdeal827_divisorAway_eq_one place]
  let z : Kˣ := x * y ^ 59
  have hz : IsDedekindDomain.selmerGroup.principalDivisorAway
      (R := NumberField.RingOfIntegers K) (K := K) (placesOver827 K) z = 1 := by
    rw [map_mul, map_pow]
    exact hdivisor
  have hzmem : z ∈
      (IsDedekindDomain.selmerGroup.principalDivisorAway
        (R := NumberField.RingOfIntegers K) (K := K)
        (placesOver827 K)).ker := hz
  rw [IsDedekindDomain.selmerGroup.principalDivisorAway_ker
    (R := NumberField.RingOfIntegers K) (K := K)] at hzmem
  let u : (placesOver827 K).unit K := ⟨z, hzmem⟩
  refine ⟨u, ?_⟩
  change QuotientGroup.mk' _ (x * y ^ 59) = QuotientGroup.mk' _ x
  rw [map_mul]
  have hpow : QuotientGroup.mk (y ^ 59) =
      (1 : Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) := by
    apply (QuotientGroup.eq_one_iff (y ^ 59)).mpr
    exact ⟨y, rfl⟩
  have hpow' :
      (QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range : Kˣ →* _) (y ^ 59) = 1 := hpow
  rw [hpow']
  exact @mul_one
    (Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) _
    ((QuotientGroup.mk'
      (powMonoidHom 59 : Kˣ →* Kˣ).range : Kˣ →* _) x)

/-- A class-silent generator retaining both its valuation receipt and a
literal 827-unit representative of the same Kummer class. -/
theorem exists_classSilent_conjugatePairUnit827
    (place : Place827 K) :
    ∃ x : Kˣ,
      (∀ v : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers K),
        ((v.valuationOfNeZero x).toAdd : ZMod 59) =
          -(FractionalIdeal.count K v
            (conjugatePairIdeal827 place :
              FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) : ZMod 59)) ∧
      ∃ u : (placesOver827 K).unit K,
        (QuotientGroup.mk (u : Kˣ) :
            Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) =
          QuotientGroup.mk x := by
  obtain ⟨realRoot, J, x, hJ, hextended, hprincipal⟩ :=
    exists_plus_principal_data827 place
  refine ⟨x, ?_, exists_sUnit_eq_kummerClass_of_plus_principal_data827
    place realRoot J x hJ hextended hprincipal⟩
  intro v
  have hspan : FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton
        (NumberField.RingOfIntegers K)⁰ (x : K)) +
        FractionalIdeal.count K v
          (((J : Ideal (NumberField.RingOfIntegers K)) :
            FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ 59) =
      FractionalIdeal.count K v
        (conjugatePairIdeal827 place :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) := by
    rw [← FractionalIdeal.count_mul K v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero)
      (pow_ne_zero 59 (FractionalIdeal.coeIdeal_ne_zero.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp J.2)))]
    rw [hprincipal]
  rw [FractionalIdeal.count_pow] at hspan
  rw [count_spanSingleton_eq_neg_valuation] at hspan
  rw [← Int.cast_neg]
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 59).mpr
  refine ⟨-FractionalIdeal.count K v
      ((J : Ideal (NumberField.RingOfIntegers K)) :
        FractionalIdeal (NumberField.RingOfIntegers K)⁰ K), ?_⟩
  linarith

/-- One plus-root principal generator whose valuation vector modulo 59 is
the negative conjugate-pair divisor and whose Kummer class retains a literal
827-unit representative. -/
noncomputable def conjugatePairUnit827 (place : Place827 K) : Kˣ :=
  Classical.choose (exists_classSilent_conjugatePairUnit827 place)

theorem conjugatePairUnit827_valuation_mod
    (place : Place827 K)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    ((v.valuationOfNeZero (conjugatePairUnit827 place)).toAdd : ZMod 59) =
      -(FractionalIdeal.count K v
        (conjugatePairIdeal827 place :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) : ZMod 59) :=
  (Classical.choose_spec
    (exists_classSilent_conjugatePairUnit827 place)).1 v

/-- The literal 827-unit retained by the plus-root construction. -/
noncomputable def conjugatePairSUnit827 (place : Place827 K) :
    (placesOver827 K).unit K :=
  Classical.choose
    (Classical.choose_spec
      (exists_classSilent_conjugatePairUnit827 place)).2

/-- The retained 827-unit represents exactly the chosen principal
generator's Kummer class. -/
theorem conjugatePairSUnit827_kummerClass
    (place : Place827 K) :
    (QuotientGroup.mk (conjugatePairSUnit827 place : Kˣ) :
        Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) =
      QuotientGroup.mk (conjugatePairUnit827 place) :=
  Classical.choose_spec
    (Classical.choose_spec
      (exists_classSilent_conjugatePairUnit827 place)).2

/-- The principal generator defines an honest source in Mathlib's
827-relaxed 59-Selmer carrier. -/
noncomputable def conjugatePairSource827 (place : Place827 K) :
    QRelaxedSelmerCarrier827 K :=
  Additive.ofMul ⟨
    QuotientGroup.mk (conjugatePairUnit827 place), by
      intro v hv
      apply (valuationOfNeZeroMod_mk_eq_one_iff_dvd v
        (conjugatePairUnit827 place)).mpr
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd
        (v.valuationOfNeZero (conjugatePairUnit827 place)).toAdd 59).mp
      rw [conjugatePairUnit827_valuation_mod,
        conjugatePairIdeal827_count_eq_zero_of_not_mem place v hv]
      simp⟩

/-- The actual q-relaxed source is the finite-S lift of its retained literal
827-unit class.  This is the kernel receipt erased by the earlier
valuation-only choice. -/
theorem fromSUnitLift_conjugatePairSUnit827
    (place : Place827 K) :
    IsDedekindDomain.selmerGroup.fromSUnitLift
        (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
        (placesOver827 K)
        (QuotientGroup.mk (conjugatePairSUnit827 place)) =
      Additive.toMul (conjugatePairSource827 place) := by
  apply Subtype.ext
  exact conjugatePairSUnit827_kummerClass place

/-- Its raw supported localization at the selected prime is nonzero. -/
theorem supportValuationAt_conjugatePairSource827_ne_zero
    (place : Place827 K) :
    supportValuationAt
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
        (S := placesOver827 K) place
        (conjugatePairSource827 place) ≠ 0 := by
  intro hzero
  change place.1.valuationOfNeZeroMod 59
      (QuotientGroup.mk (conjugatePairUnit827 place)) = 1 at hzero
  have hdvd : (59 : ℤ) ∣
      (place.1.valuationOfNeZero (conjugatePairUnit827 place)).toAdd :=
    (valuationOfNeZeroMod_mk_eq_one_iff_dvd place.1
      (conjugatePairUnit827 place)).mp hzero
  have hcast :
      ((place.1.valuationOfNeZero
        (conjugatePairUnit827 place)).toAdd : ZMod 59) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 59).mpr hdvd
  rw [conjugatePairUnit827_valuation_mod] at hcast
  exact neg_conjugatePairIdeal827_count_selected_ne_zero place hcast

end Fermat.FiftyNine.Conservation.ConjugatePairSource827
