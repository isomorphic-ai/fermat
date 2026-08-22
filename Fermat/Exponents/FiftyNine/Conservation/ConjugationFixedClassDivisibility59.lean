/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Divisibility of conjugation-fixed ideal classes at conductor 59

The checked maximal-real class-number certificate makes the 59th-power map
bijective on the class group of the maximal real subfield.  If an ideal of
the full cyclotomic field is fixed by complex conjugation, its extended
relative norm is its square.  Taking a 59th root of the norm class and using
`2 * 30 - 59 = 1` therefore constructs a 59th root of the original ideal
class upstairs.

This is a class-group theorem only.  It does not select an 827 divisor,
construct a Selmer class, or assert that a finite-S obstruction vanishes.
-/
import Fermat.Exponents.FiftyNine.Conservation.Fold
import Mathlib.RingTheory.ClassGroup.ExtendedHom

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.ConjugationFixedClassDivisibility59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

set_option maxRecDepth 2000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

local notation3 "K⁺" => NumberField.maximalRealSubfield K

private theorem plusClassGroup_card_coprime_fiftyNine :
    Nat.Coprime (Nat.card (ClassGroup (NumberField.RingOfIntegers K⁺))) 59 := by
  rw [Nat.card_eq_fintype_card]
  apply Nat.Coprime.symm
  exact (by norm_num : Nat.Prime 59).coprime_iff_not_dvd.mpr
    (Fold.not_dvd_plusClassNumber (K := K))

/-- A nonzero conjugation-fixed integral ideal of the conductor-59
cyclotomic field has a 59-divisible ideal class.

The root is constructed from a 59th root of the relative-norm class over
the maximal real subfield.  No assertion about the minus class group is
used: conjugation-fixity is the precise guard that seats the ideal in the
real fold. -/
theorem exists_class_pow_fiftyNine_eq_of_conjugation_fixed
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ 0)
    (hfixed :
      I.map (NumberField.IsCMField.ringOfIntegersComplexConj K) = I) :
    ∃ rootClass : ClassGroup (NumberField.RingOfIntegers K),
      rootClass ^ 59 =
        ClassGroup.mk0
          ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ := by
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
            (NumberField.RingOfIntegers K) (realRoot ^ 59) := by
            rw [map_pow]
      _ = ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
          (NumberField.RingOfIntegers K) normClass := by
            exact congrArg
              (ClassGroup.extendedHom (NumberField.RingOfIntegers K⁺)
                (NumberField.RingOfIntegers K)) hrealRoot
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
  refine ⟨extendedRoot ^ 30 * idealClass⁻¹, ?_⟩
  rw [mul_pow, inv_pow]
  calc
    (extendedRoot ^ 30) ^ 59 * (idealClass ^ 59)⁻¹ =
        (extendedRoot ^ 59) ^ 30 * (idealClass ^ 59)⁻¹ := by
          congr 1
          calc
            (extendedRoot ^ 30) ^ 59 = extendedRoot ^ (30 * 59) :=
              (pow_mul extendedRoot 30 59).symm
            _ = extendedRoot ^ (59 * 30) := by norm_num
            _ = (extendedRoot ^ 59) ^ 30 :=
              pow_mul extendedRoot 59 30
    _ = (idealClass ^ 2) ^ 30 * (idealClass ^ 59)⁻¹ := by
          rw [hextendedRoot]
    _ = idealClass := by
          group

end Fermat.FiftyNine.Conservation.ConjugationFixedClassDivisibility59
