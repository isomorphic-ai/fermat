/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The honest degree-58 local cyclotomic trace at 59

This file installs the finite-dimensional algebra structure from the rational
59-adic completion into the pinned valuation completion of the 59th
cyclotomic field at `lambda = zeta_59 - 1`.

The upper degree bound comes from the dense scalar-extension map

`Q_59 ⊗_ℚ K → K_lambda`.

For the reverse bound, `Phi_59(X + 1)` is transported to the completed
rational integer ring.  It remains Eisenstein at `(59)`, and the local
cyclotomic uniformizer is a root.  Its minimal polynomial therefore has
degree 58.  The two bounds meet, giving

`finrank Q_59 K_lambda = 58`.

Consequently the genuine algebra trace is available and satisfies

`Tr_{K_lambda / Q_59}(x) = 58 * x`

on rational-completion scalars.  This is structural completion and trace
infrastructure only.  It does not identify a package finite logarithm with a
completed p-adic logarithm, a Hilbert symbol, or an Artin--Hasse reciprocity
formula; those remain separate comparison theorems.
-/
import KummerCriterion.CyclotomicUnits.DworkParameter.Part16
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral

open scoped NumberField Topology TensorProduct Valued

noncomputable section

namespace Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59

open KummerCriterion.Furtwaengler.KummerArtinHasse
open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open Polynomial

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The rational completion at `(59)`. -/
abbrev RationalCompletion59 : Type :=
  (lambdaRationalHeightOneSpectrum 59).adicCompletion ℚ

/-- The integer ring in the rational completion at `(59)`. -/
abbrev RationalIntegerRing59 : Type :=
  (lambdaRationalHeightOneSpectrum 59).adicCompletionIntegers ℚ

/-- The pinned valuation completion of the cyclotomic field at `lambda`. -/
abbrev LambdaCompletion59 : Type := LambdaValuedCompletion 59 K

/- The completion scalar actions use the canonical global rational action.
This local algebra instance removes the competing generic `RatAlgebra`
diamond while proving coherence; it need not be exported. -/
local instance : Algebra ℚ (LambdaCompletion59 K) :=
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
    (R := NumberField.RingOfIntegers K) (K := K) (S := ℚ)
      (lambdaHeightOneSpectrum 59 K)

/-- The existing continuous completion map, installed as a reusable algebra
structure. -/
instance instAlgebraRationalCompletionLambdaCompletion59 :
    Algebra RationalCompletion59 (LambdaCompletion59 K) :=
  rationalCompletionToLambdaAlgebra (p := 59) (K := K)

/-- Compatibility of the completed rational map with rational scalars. -/
theorem algebraMap_rat_compat (x : ℚ) :
    algebraMap RationalCompletion59 (LambdaCompletion59 K)
        (algebraMap ℚ RationalCompletion59 x) =
      algebraMap ℚ (LambdaCompletion59 K) x := by
  change rationalToLambdaCompletionRingHom (p := 59) (K := K)
      (algebraMap ℚ RationalCompletion59 x) =
    algebraMap ℚ (LambdaCompletion59 K) x
  rw [show algebraMap ℚ RationalCompletion59 x =
      ((WithVal.equiv
        ((lambdaRationalHeightOneSpectrum 59).valuation ℚ)).symm x :
          RationalCompletion59) from rfl]
  rw [rationalToLambdaCompletionRingHom_coe]
  simp [rationalToLambdaWithValRingHom,
    rationalToLambdaComapWithValRingHom]
  exact map_ratCast (algebraMap K (LambdaCompletion59 K)) x

/-- Rational scalars, completed rational scalars, and local cyclotomic
scalars form a coherent scalar tower. -/
instance instIsScalarTowerRatRationalCompletionLambdaCompletion59 :
    IsScalarTower ℚ RationalCompletion59 (LambdaCompletion59 K) :=
  ⟨fun (x : ℚ) (y : RationalCompletion59)
      (z : LambdaCompletion59 K) => by
    simp only [Algebra.smul_def, map_mul, algebraMap_rat_compat K]
    rw [mul_assoc]⟩

/-- Scalar multiplication through the completed rational embedding is
continuous. -/
instance instContinuousSMulRationalCompletionLambdaCompletion59 :
    ContinuousSMul RationalCompletion59 (LambdaCompletion59 K) :=
  continuousSMul_of_algebraMap _ _
    (continuous_algebraMap_rationalCompletionToLambdaAlgebra
      (p := 59) (K := K))

/-- The dense scalar-extension map from the global cyclotomic field to its
local completion. -/
def localTensorMap59 :
    RationalCompletion59 ⊗[ℚ] K →ₗ[RationalCompletion59]
      LambdaCompletion59 K :=
  Algebra.TensorProduct.lift
    (Algebra.algHom RationalCompletion59 RationalCompletion59
      (LambdaCompletion59 K))
    (Algebra.algHom ℚ K (LambdaCompletion59 K))
    (fun _ _ ↦ mul_comm ..) |>.toLinearMap

/-- Density plus finite-dimensional closedness makes the scalar-extension
map surjective. -/
theorem localTensorMap59_surjective :
    Function.Surjective (localTensorMap59 K) := by
  let Φ := localTensorMap59 K
  have h_dense : DenseRange Φ := by
    apply ((lambdaHeightOneSpectrum 59 K).denseRange_algebraMap K).mono
    rintro _ ⟨l, rfl⟩
    exact ⟨1 ⊗ₜ l, by simp [Φ, localTensorMap59, Algebra.algHom]⟩
  rw [← Set.range_eq_univ, ← Φ.coe_range,
      ← Φ.range.closed_of_finiteDimensional.closure_eq]
  exact h_dense.closure_range

/-- The actual local completion is finite-dimensional over the rational
completion. -/
instance instModuleFiniteRationalCompletionLambdaCompletion59 :
    Module.Finite RationalCompletion59 (LambdaCompletion59 K) :=
  Module.Finite.of_surjective (localTensorMap59 K)
    (localTensorMap59_surjective K)

/-! ## The Eisenstein lower bound -/

/-- The shifted cyclotomic polynomial over the integers. -/
def shiftedCyclotomic59Int : ℤ[X] :=
  (cyclotomic 59 ℤ).comp (X + 1)

/-- The shifted cyclotomic polynomial over the rational completed integer
ring. -/
def shiftedCyclotomic59PadicInt : RationalIntegerRing59[X] :=
  shiftedCyclotomic59Int.map
    (algebraMap ℤ RationalIntegerRing59)

theorem shiftedCyclotomic59Int_monic : shiftedCyclotomic59Int.Monic := by
  apply (cyclotomic.monic 59 ℤ).comp (monic_X_add_C 1)
  change (X + C (1 : ℤ)).natDegree ≠ 0
  rw [natDegree_X_add_C]
  norm_num

theorem shiftedCyclotomic59PadicInt_monic :
    shiftedCyclotomic59PadicInt.Monic := by
  exact shiftedCyclotomic59Int_monic.map
    (algebraMap ℤ RationalIntegerRing59)

/-- The rational uniformizer `59` has valuation exactly one and hence does
not lie in the square of the rational maximal ideal. -/
theorem natCast_prime_not_mem_rationalPadicPrimeIdeal_sq :
    (59 : RationalIntegerRing59) ∉ (rationalPadicPrimeIdeal 59) ^ 2 := by
  change ¬ ((59 : RationalIntegerRing59) ∈
    (((rationalPadicPrimeIdeal 59) ^ 2 : Ideal RationalIntegerRing59) :
      Set RationalIntegerRing59))
  rw [rationalPadicPrimeIdeal_pow_eq_valuation_closedBall (p := 59) 2]
  simp only [Set.mem_setOf_eq]
  change ¬ Valued.v (59 : RationalCompletion59) ≤
    Valued.v ((59 : RationalCompletion59) ^ 2)
  have hcoe :
      (((59 : RationalIntegerRing59) : RationalCompletion59)) =
        (59 : RationalCompletion59) := rfl
  have hp :
      Valued.v (59 : RationalCompletion59) = WithZero.exp (-1 : ℤ) := by
    rw [← hcoe]
    exact
      rationalPadicInteger_natCast_prime_valuation_eq_exp_neg_one (p := 59)
  rw [map_pow, hp]
  simp only [← WithZero.exp_nsmul]
  rw [WithZero.exp_le_exp]
  norm_num

theorem shiftedCyclotomic59PadicInt_coeff_zero :
    shiftedCyclotomic59PadicInt.coeff 0 =
      (59 : RationalIntegerRing59) := by
  rw [shiftedCyclotomic59PadicInt, coeff_map]
  change algebraMap ℤ RationalIntegerRing59
      (shiftedCyclotomic59Int.coeff 0) =
    (59 : RationalIntegerRing59)
  rw [shiftedCyclotomic59Int, coeff_zero_eq_eval_zero, eval_comp,
    cyclotomic_prime, eval_add, eval_X, eval_one, zero_add,
    eval_geom_sum, one_geom_sum]
  simp

/-- `Phi_59(X + 1)` remains Eisenstein after passage to the completed
rational integer ring. -/
theorem shiftedCyclotomic59PadicInt_isEisenstein :
    shiftedCyclotomic59PadicInt.IsEisensteinAt
      (rationalPadicPrimeIdeal 59) := by
  refine shiftedCyclotomic59PadicInt_monic.isEisensteinAt_of_mem_of_notMem
    ?_ ?_ ?_
  · rw [rationalPadicPrimeIdeal_eq_maximalIdeal]
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  · intro n hn
    have hdeg :
        shiftedCyclotomic59PadicInt.natDegree =
          shiftedCyclotomic59Int.natDegree := by
      simpa [shiftedCyclotomic59PadicInt] using
        shiftedCyclotomic59Int_monic.natDegree_map
          (algebraMap ℤ RationalIntegerRing59)
    have hsrc :=
      (cyclotomic_comp_X_add_one_isEisensteinAt 59).mem (hdeg ▸ hn)
    rw [shiftedCyclotomic59PadicInt, coeff_map]
    rw [rationalPadicPrimeIdeal, Ideal.mem_span_singleton]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hsrc
    refine ⟨algebraMap ℤ RationalIntegerRing59 c, ?_⟩
    calc
      algebraMap ℤ RationalIntegerRing59
          (shiftedCyclotomic59Int.coeff n) =
          algebraMap ℤ RationalIntegerRing59 ((59 : ℤ) * c) := by
            apply congrArg (algebraMap ℤ RationalIntegerRing59)
            simpa [shiftedCyclotomic59Int] using hc
      _ = algebraMap ℤ RationalIntegerRing59 (59 : ℤ) *
          algebraMap ℤ RationalIntegerRing59 c := by rw [map_mul]
      _ = (59 : RationalIntegerRing59) *
          algebraMap ℤ RationalIntegerRing59 c := by norm_num
  · rw [shiftedCyclotomic59PadicInt_coeff_zero]
    exact natCast_prime_not_mem_rationalPadicPrimeIdeal_sq

theorem shiftedCyclotomic59Int_natDegree :
    shiftedCyclotomic59Int.natDegree = 58 := by
  rw [shiftedCyclotomic59Int, natDegree_comp]
  · rw [natDegree_cyclotomic, Nat.totient_prime (by decide)]
    change 58 * (X + 1 : ℤ[X]).natDegree = 58
    change 58 * (X + C (1 : ℤ)).natDegree = 58
    rw [natDegree_X_add_C]

theorem shiftedCyclotomic59PadicInt_natDegree :
    shiftedCyclotomic59PadicInt.natDegree = 58 := by
  rw [show shiftedCyclotomic59PadicInt.natDegree =
      shiftedCyclotomic59Int.natDegree by
    simpa [shiftedCyclotomic59PadicInt] using
      shiftedCyclotomic59Int_monic.natDegree_map
        (algebraMap ℤ RationalIntegerRing59)]
  exact shiftedCyclotomic59Int_natDegree

theorem shiftedCyclotomic59PadicInt_irreducible :
    Irreducible shiftedCyclotomic59PadicInt := by
  apply shiftedCyclotomic59PadicInt_isEisenstein.irreducible
  · rw [rationalPadicPrimeIdeal_eq_maximalIdeal]
    exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  · exact shiftedCyclotomic59PadicInt_monic.isPrimitive
  · rw [shiftedCyclotomic59PadicInt_natDegree]
    norm_num

/-- The same polynomial over the rational 59-adic completion. -/
def shiftedCyclotomic59Q : RationalCompletion59[X] :=
  shiftedCyclotomic59PadicInt.map
    (algebraMap RationalIntegerRing59 RationalCompletion59)

theorem shiftedCyclotomic59Q_monic : shiftedCyclotomic59Q.Monic :=
  shiftedCyclotomic59PadicInt_monic.map
    (algebraMap RationalIntegerRing59 RationalCompletion59)

theorem shiftedCyclotomic59Q_natDegree :
    shiftedCyclotomic59Q.natDegree = 58 := by
  rw [shiftedCyclotomic59Q,
    shiftedCyclotomic59PadicInt_monic.natDegree_map]
  exact shiftedCyclotomic59PadicInt_natDegree

theorem shiftedCyclotomic59Q_irreducible :
    Irreducible shiftedCyclotomic59Q := by
  exact shiftedCyclotomic59PadicInt_monic
    |>.irreducible_iff_irreducible_map_fraction_map.mp
      shiftedCyclotomic59PadicInt_irreducible

/-! ## The local cyclotomic root and exact degree -/

theorem valuedCyclotomicLambda_add_one_eq_zeta :
    valuedCyclotomicLambda 59 K + 1 = valuedCyclotomicZeta 59 K := by
  change
    ((algebraMap (NumberField.RingOfIntegers K) (LambdaCompletion59 K))
        ((IsCyclotomicExtension.zeta_spec 59 ℚ K).toInteger - 1) :
      LambdaCompletion59 K) + 1 =
      algebraMap (NumberField.RingOfIntegers K) (LambdaCompletion59 K)
        (IsCyclotomicExtension.zeta_spec 59 ℚ K).toInteger
  rw [map_sub, map_one, sub_add_cancel]

theorem valuedCyclotomicZeta_isPrimitiveRoot :
    IsPrimitiveRoot (valuedCyclotomicZeta 59 K) 59 := by
  change IsPrimitiveRoot
    (algebraMap K (LambdaCompletion59 K)
      (IsCyclotomicExtension.zeta 59 ℚ K)) 59
  exact (IsCyclotomicExtension.zeta_spec 59 ℚ K).map_of_injective
    (algebraMap K (LambdaCompletion59 K)).injective

theorem shiftedCyclotomic59Q_eq_map_int :
    shiftedCyclotomic59Q =
      shiftedCyclotomic59Int.map
        (algebraMap ℤ RationalCompletion59) := by
  rw [shiftedCyclotomic59Q, shiftedCyclotomic59PadicInt, map_map]
  congr 1

theorem shiftedCyclotomic59Q_aeval_valuedCyclotomicLambda :
    aeval (valuedCyclotomicLambda 59 K) shiftedCyclotomic59Q = 0 := by
  rw [aeval_def]
  rw [shiftedCyclotomic59Q_eq_map_int]
  rw [eval₂_map]
  rw [shiftedCyclotomic59Int, eval₂_comp]
  simp only [eval₂_add, eval₂_X, eval₂_one]
  rw [valuedCyclotomicLambda_add_one_eq_zeta K]
  have hcomp :
      (algebraMap RationalCompletion59 (LambdaCompletion59 K)).comp
          (algebraMap ℤ RationalCompletion59) =
        algebraMap ℤ (LambdaCompletion59 K) := by
    ext z
    simp
  rw [hcomp]
  have hz := (valuedCyclotomicZeta_isPrimitiveRoot K).isRoot_cyclotomic
    (by norm_num : 0 < (59 : ℕ))
  rw [Polynomial.IsRoot.def] at hz
  simpa [← eval_map, map_cyclotomic] using hz

theorem minpoly_valuedCyclotomicLambda59 :
    minpoly RationalCompletion59 (valuedCyclotomicLambda 59 K) =
      shiftedCyclotomic59Q := by
  exact (minpoly.eq_of_irreducible_of_monic
    shiftedCyclotomic59Q_irreducible
    (shiftedCyclotomic59Q_aeval_valuedCyclotomicLambda K)
    shiftedCyclotomic59Q_monic).symm

theorem localFinrank59_lower :
    58 ≤ Module.finrank RationalCompletion59 (LambdaCompletion59 K) := by
  rw [← shiftedCyclotomic59Q_natDegree,
    ← minpoly_valuedCyclotomicLambda59 K]
  exact minpoly.natDegree_le (valuedCyclotomicLambda 59 K)

theorem globalCyclotomicFinrank59 : Module.finrank ℚ K = 58 := by
  rw [IsCyclotomicExtension.finrank (K := ℚ) (L := K)
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos 59)),
    Nat.totient_prime (by decide : Nat.Prime 59)]

theorem localFinrank59_upper :
    Module.finrank RationalCompletion59 (LambdaCompletion59 K) ≤ 58 := by
  calc
    Module.finrank RationalCompletion59 (LambdaCompletion59 K) ≤
        Module.finrank RationalCompletion59
          (RationalCompletion59 ⊗[ℚ] K) :=
      LinearMap.finrank_le_finrank_of_surjective
        (localTensorMap59_surjective K)
    _ = Module.finrank ℚ K := Module.finrank_baseChange
    _ = 58 := globalCyclotomicFinrank59 K

/-- The actual lambda completion has the full cyclotomic local degree 58. -/
theorem localFinrank59 :
    Module.finrank RationalCompletion59 (LambdaCompletion59 K) = 58 :=
  Nat.le_antisymm (localFinrank59_upper K) (localFinrank59_lower K)

/-! ## Honest local trace on base scalars -/

/-- Trace of a rational-completion scalar is multiplication by the local
degree 58. -/
theorem localTrace59_algebraMap (x : RationalCompletion59) :
    Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
        (algebraMap RationalCompletion59 (LambdaCompletion59 K) x) =
      58 • x := by
  rw [Algebra.trace_algebraMap, localFinrank59 K]

/-- The same trace formula on an embedded rational scalar. -/
theorem localTrace59_algebraMap_rat (x : ℚ) :
    Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
        (algebraMap RationalCompletion59 (LambdaCompletion59 K)
          (algebraMap ℚ RationalCompletion59 x)) =
      algebraMap ℚ RationalCompletion59 (58 * x) := by
  rw [localTrace59_algebraMap]
  simp only [nsmul_eq_mul]
  rw [map_mul]
  norm_num

end Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59
