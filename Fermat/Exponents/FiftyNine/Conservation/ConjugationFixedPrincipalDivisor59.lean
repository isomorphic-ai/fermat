/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Principal representatives for conjugation-fixed classes at conductor 59

The preceding class-divisibility theorem produces a 59th root in the class
group.  This file chooses an honest nonzero integral ideal representing that
root and uses equality in the class group to recover a principal fractional
ideal equation.  Factoring this equation exposes the valuation congruence
needed by a later q-relaxed Selmer construction.

No 827 divisor is selected here, and no finite-S obstruction is declared to
vanish.
-/
import Fermat.Exponents.FiftyNine.Conservation.ConjugationFixedClassDivisibility59
import Fermat.Experiments.Conservation.SelmerSequence

open scoped nonZeroDivisors NumberField WithZero

noncomputable section

namespace Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

set_option maxRecDepth 2000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

abbrev IntegerIdeal59 (K : Type) [Field K] [NumberField K] :=
  Ideal (NumberField.RingOfIntegers K)

/-- A conjugation-fixed ideal is the principal divisor of an element times
a 59th ideal power.  The auxiliary ideal is genuine and nonzero because it
is selected through `ClassGroup.mk0_surjective`. -/
theorem exists_principal_times_ideal_pow_fiftyNine_eq
    (I : IntegerIdeal59 K) (hI : I ≠ 0)
    (hfixed :
      I.map (NumberField.IsCMField.ringOfIntegersComplexConj K) = I) :
    ∃ (J : (Ideal (NumberField.RingOfIntegers K))⁰) (x : Kˣ),
      FractionalIdeal.spanSingleton
          (NumberField.RingOfIntegers K)⁰ (x : K) *
        ((J : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ 59 =
        (I : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) := by
  obtain ⟨rootClass, hrootClass⟩ :=
    Fermat.FiftyNine.Conservation.ConjugationFixedClassDivisibility59.exists_class_pow_fiftyNine_eq_of_conjugation_fixed
      I hI hfixed
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective rootClass
  let I₀ : (Ideal (NumberField.RingOfIntegers K))⁰ :=
    ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  have hclasses : ClassGroup.mk0 (J ^ 59) = ClassGroup.mk0 I₀ := by
    rw [map_pow, hJ]
    exact hrootClass
  obtain ⟨x, hx, hprincipal⟩ :=
    (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring (K := K)).mp hclasses
  refine ⟨J, Units.mk0 x hx, ?_⟩
  have hJpow :
      (((J ^ 59 : (Ideal (NumberField.RingOfIntegers K))⁰) :
          Ideal (NumberField.RingOfIntegers K)) :
        FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) =
      ((J : Ideal (NumberField.RingOfIntegers K)) :
        FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ 59 := by
    exact FractionalIdeal.coeIdeal_pow
      (S := (NumberField.RingOfIntegers K)⁰) (P := K) J 59
  rw [← hJpow]
  simpa only [Units.val_mk0, FractionalIdeal.coe_mk0, I₀] using hprincipal

omit [IsCyclotomicExtension {59} ℚ K] in
/-- Fractional-ideal factorization of a principal field unit is the negative
of its additive height-one valuation.  This public spelling is the
coordinate bridge needed to read the principal equation modulo 59. -/
theorem count_spanSingleton_eq_neg_valuation
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) (x : Kˣ) :
    FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton
          (NumberField.RingOfIntegers K)⁰ (x : K)) =
      -(v.valuationOfNeZero x).toAdd := by
  let s := IsLocalization.sec (NumberField.RingOfIntegers K)⁰ (x : K)
  have hs : FractionalIdeal.spanSingleton
      (NumberField.RingOfIntegers K)⁰ (x : K) =
      FractionalIdeal.spanSingleton
          (NumberField.RingOfIntegers K)⁰
          (algebraMap (NumberField.RingOfIntegers K) K (s.2 :
            NumberField.RingOfIntegers K))⁻¹ *
        (Ideal.span {s.1} :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    symm
    rw [inv_mul_eq_iff_eq_mul₀ (map_ne_zero_of_mem_nonZeroDivisors _
      (IsFractionRing.injective (NumberField.RingOfIntegers K) K)
        s.2.property)]
    exact IsLocalization.sec_spec'
      (NumberField.RingOfIntegers K)⁰ (x : K)
  rw [FractionalIdeal.count_well_defined K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero) hs]
  simp [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero,
    IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroToFun, s]
  ring

/-- The principal representative of a conjugation-fixed ideal has, modulo
59, the negative of that ideal's factorization coordinate at every
height-one place. -/
theorem exists_unit_valuation_mod_fiftyNine_eq_neg_count
    (I : IntegerIdeal59 K) (hI : I ≠ 0)
    (hfixed :
      I.map (NumberField.IsCMField.ringOfIntegersComplexConj K) = I) :
    ∃ x : Kˣ, ∀ v : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K),
      ((v.valuationOfNeZero x).toAdd : ZMod 59) =
        -(FractionalIdeal.count K v
          (I : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) :
            ZMod 59) := by
  obtain ⟨J, x, hx⟩ :=
    exists_principal_times_ideal_pow_fiftyNine_eq I hI hfixed
  refine ⟨x, ?_⟩
  intro v
  have hspan : FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton
        (NumberField.RingOfIntegers K)⁰ (x : K)) +
        FractionalIdeal.count K v
          (((J : Ideal (NumberField.RingOfIntegers K)) :
            FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ 59) =
      FractionalIdeal.count K v
        (I : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) := by
    rw [← FractionalIdeal.count_mul K v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero)
      (pow_ne_zero 59 (FractionalIdeal.coeIdeal_ne_zero.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp J.2)))]
    rw [hx]
  rw [FractionalIdeal.count_pow] at hspan
  rw [count_spanSingleton_eq_neg_valuation] at hspan
  rw [← Int.cast_neg]
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 59).mpr
  refine ⟨-FractionalIdeal.count K v
      ((J : Ideal (NumberField.RingOfIntegers K)) :
        FractionalIdeal (NumberField.RingOfIntegers K)⁰ K), ?_⟩
  linarith

end Fermat.FiftyNine.Conservation.ConjugationFixedPrincipalDivisor59
