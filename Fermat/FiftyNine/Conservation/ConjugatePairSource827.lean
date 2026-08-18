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
import Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59
import Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59

open scoped nonZeroDivisors NumberField Pointwise

noncomputable section

namespace Fermat.FiftyNine.Conservation.ConjugatePairSource827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

set_option maxRecDepth 2000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : DecidableEq
    (IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :=
  Classical.decEq _

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

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

/-- One principal generator whose valuation vector modulo 59 is the
negative conjugate-pair divisor. -/
noncomputable def conjugatePairUnit827 (place : Place827 K) : Kˣ :=
  Classical.choose <|
    exists_unit_valuation_mod_fiftyNine_eq_neg_count
      (conjugatePairIdeal827 place)
      (conjugatePairIdeal827_ne_zero place)
      (conjugatePairIdeal827_fixed place)

theorem conjugatePairUnit827_valuation_mod
    (place : Place827 K)
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    ((v.valuationOfNeZero (conjugatePairUnit827 place)).toAdd : ZMod 59) =
      -(FractionalIdeal.count K v
        (conjugatePairIdeal827 place :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) : ZMod 59) :=
  (Classical.choose_spec <|
    exists_unit_valuation_mod_fiftyNine_eq_neg_count
      (conjugatePairIdeal827 place)
      (conjugatePairIdeal827_ne_zero place)
      (conjugatePairIdeal827_fixed place)) v

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
