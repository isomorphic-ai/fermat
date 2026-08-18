/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Separation of triangular norm factors at 59

The explicit triangular norm factors have perturbations
`c_j^59 * (60 * lambda)^j`.  For `1 ≤ j ≤ 58`, their nonzero valuations are
pairwise distinct modulo 59, so the generic dominant-term theorem forbids
them from cancelling.  If their product enters `U_59`, every perturbation
enters `U_59` individually and the monomial depth gap pushes each into
`U_60`.
-/
import Fermat.Conservation.PrimeTriangularExplicitNorm
import Fermat.Conservation.PrimeTriangularValuationDepth
import Fermat.Conservation.ValuationProductDominant
import Fermat.FiftyNine.Conservation.ExplicitNormResidue59
import Mathlib.Tactic

open scoped NumberField WithZero BigOperators
open Polynomial

noncomputable section

namespace Fermat.FiftyNine.Conservation.TriangularNormSeparation59

open Fermat.Conservation.PrimeTriangularUnitFactorization
open Fermat.Conservation.PrimeTriangularValuationDepth
open Fermat.Conservation.PrimeTriangularExplicitNorm
open Fermat.Conservation.ValuationProductDominant
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59
open Fermat.FiftyNine.Conservation.ExplicitNormResidue59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- Distinct exponents between `1` and `58` give distinct nonzero monomial
valuations, because their difference cannot be a nonzero multiple of 59. -/
theorem twistedMonomialValuation_ne
    (c d : LambdaField59 K) (j k : ℕ)
    (hj0 : 0 < j) (hj59 : j < 59)
    (hk0 : 0 < k) (hk59 : k < 59)
    (hc0 : c ≠ 0) (hd0 : d ≠ 0) (hjk : j ≠ k) :
    Valued.v (c ^ 59 * twistedLambda59 K ^ j) ≠
      Valued.v (d ^ 59 * twistedLambda59 K ^ k) := by
  have hcval :
      Valued.v (c ^ 59 * twistedLambda59 K ^ j) =
        Valued.v c ^ 59 * WithZero.exp (-1 : ℤ) ^ j := by
    rw [map_mul, map_pow, map_pow, twistedLambda59_valuation]
  have hdval :
      Valued.v (d ^ 59 * twistedLambda59 K ^ k) =
        Valued.v d ^ 59 * WithZero.exp (-1 : ℤ) ^ k := by
    rw [map_mul, map_pow, map_pow, twistedLambda59_valuation]
  rw [hcval, hdval]
  cases hvc : Valued.v c with
  | zero =>
      exfalso
      exact hc0 ((Valuation.zero_iff
        (Valued.v : Valuation (LambdaField59 K) ℤᵐ⁰)).mp hvc)
  | coe zc =>
      cases hvd : Valued.v d with
      | zero =>
          exfalso
          exact hd0 ((Valuation.zero_iff
            (Valued.v : Valuation (LambdaField59 K) ℤᵐ⁰)).mp hvd)
      | coe zd =>
          let mc : ℤ := Multiplicative.toAdd zc
          let md : ℤ := Multiplicative.toAdd zd
          have hzc : (↑zc : ℤᵐ⁰) = WithZero.exp mc := by rfl
          have hzd : (↑zd : ℤᵐ⁰) = WithZero.exp md := by rfl
          rw [hzc, hzd]
          simp only [← WithZero.exp_nsmul, ← WithZero.exp_add,
            nsmul_eq_mul]
          intro heq
          have heq' := WithZero.exp_inj.mp heq
          have hdvd : (59 : ℤ) ∣ (j : ℤ) - k := by
            use mc - md
            omega
          have habs : |(j : ℤ) - k| < 59 := by omega
          have hzero : (j : ℤ) - k = 0 := by
            obtain ⟨t, ht⟩ := hdvd
            have htBounds := abs_lt.mp habs
            rw [ht] at htBounds
            have ht0 : t = 0 := by omega
            rw [ht, ht0]
            norm_num
          exact hjk (by omega)

/-- The perturbation in the explicit norm of the `j`th triangular factor. -/
def triangularNormPerturbation59
    (f : (LambdaField59 K)[X]) (j : ℕ) : LambdaField59 K :=
  triangularCoefficient f j ^ 59 * twistedLambda59 K ^ j

theorem triangularCoefficient_valuation_le_one
    (f : (LambdaField59 K)[X])
    (hf : ∀ k : ℕ, 0 < k → Valued.v (f.coeff k) ≤ 1)
    (j : ℕ) (hj0 : 0 < j) :
    Valued.v (triangularCoefficient f j) ≤ 1 := by
  rw [triangularCoefficient]
  apply (Valued.v : Valuation (LambdaField59 K) ℤᵐ⁰).map_sub_le
  · exact hf j hj0
  · simpa using
      (triangularProduct_coefficient_depth f 0 (by simpa using hf) (j - 1)).1
        j hj0

theorem triangularNormPerturbation59_valuation_lt_one
    (f : (LambdaField59 K)[X])
    (hf : ∀ k : ℕ, 0 < k → Valued.v (f.coeff k) ≤ 1)
    (j : ℕ) (hj0 : 0 < j) :
    Valued.v (triangularNormPerturbation59 K f j) < 1 := by
  rw [triangularNormPerturbation59, map_mul, map_pow, map_pow,
    twistedLambda59_valuation]
  have hc := triangularCoefficient_valuation_le_one K f hf j hj0
  have hcpow : Valued.v (triangularCoefficient f j) ^ 59 ≤ 1 := by
    simpa using pow_le_one₀
      (show 0 ≤ Valued.v (triangularCoefficient f j) from bot_le) hc
  calc
    Valued.v (triangularCoefficient f j) ^ 59 *
          WithZero.exp (-1 : ℤ) ^ j ≤
        1 * WithZero.exp (-1 : ℤ) ^ j :=
      mul_le_mul_left hcpow _
    _ = WithZero.exp (-(j : ℤ)) := by
      rw [one_mul, ← WithZero.exp_nsmul]
      congr 1
      simp only [nsmul_eq_mul]
      omega
    _ < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega

/-- A depth bound on the whole triangular norm product applies separately
to every elementary perturbation. -/
theorem each_triangularNormPerturbation59_valuation_le
    (f : (LambdaField59 K)[X])
    (hf : ∀ k : ℕ, 0 < k → Valued.v (f.coeff k) ≤ 1)
    (bound : ℤᵐ⁰)
    (hprod :
      Valued.v
          ((∏ j ∈ Finset.Icc 1 58,
              (1 + triangularNormPerturbation59 K f j)) - 1) ≤ bound) :
    ∀ j ∈ Finset.Icc 1 58,
      Valued.v (triangularNormPerturbation59 K f j) ≤ bound := by
  apply each_valuation_le_of_prod_one_add_sub_one_le
    (Valued.v : Valuation (LambdaField59 K) ℤᵐ⁰)
      (Finset.Icc 1 58) (triangularNormPerturbation59 K f) bound
  · intro j hj
    exact triangularNormPerturbation59_valuation_lt_one K f hf j
      (Finset.mem_Icc.mp hj).1
  · intro j hj k hk hj0 hk0 hjk
    have hjBounds := Finset.mem_Icc.mp hj
    have hkBounds := Finset.mem_Icc.mp hk
    have hc0 : triangularCoefficient f j ≠ 0 := by
      intro hc
      apply hj0
      simp [triangularNormPerturbation59, hc]
    have hd0 : triangularCoefficient f k ≠ 0 := by
      intro hc
      apply hk0
      simp [triangularNormPerturbation59, hc]
    exact twistedMonomialValuation_ne K
      (triangularCoefficient f j) (triangularCoefficient f k) j k
      (by omega) (by omega) (by omega) (by omega) hc0 hd0 hjk
  · exact hprod

/-- Once the triangular norm product enters `U_59`, every elementary
perturbation is individually in `U_60`. -/
theorem triangularNormPerturbations59_mem_U60_of_product_mem_U59
    (f : (LambdaField59 K)[X])
    (hf : ∀ k : ℕ, 0 < k → Valued.v (f.coeff k) ≤ 1)
    (hprod :
      Valued.v
          ((∏ j ∈ Finset.Icc 1 58,
              (1 + triangularNormPerturbation59 K f j)) - 1) ≤
        WithZero.exp (-59 : ℤ)) :
    ∀ j ∈ Finset.Icc 1 58,
      Valued.v (triangularNormPerturbation59 K f j) ≤
        WithZero.exp (-60 : ℤ) := by
  intro j hj
  have hjBounds := Finset.mem_Icc.mp hj
  apply monomialDepthGap59 K (triangularCoefficient f j) j
    (by omega) (by omega)
  exact each_triangularNormPerturbation59_valuation_le K f hf _ hprod j hj

/-- Field-norm form of the preceding theorem, using the exact generic norm
formula for the complete evaluated triangular product. -/
theorem triangularNormPerturbations59_mem_U60_of_norm_mem_U59
    (f : (LambdaField59 K)[X])
    (hf : ∀ k : ℕ, 0 < k → Valued.v (f.coeff k) ≤ 1)
    (hnorm :
      Valued.v
          (Algebra.norm (LambdaField59 K)
              (aeval (twistedLambdaRoot59 K) (triangularProduct f 58)) - 1) ≤
        WithZero.exp (-59 : ℤ)) :
    ∀ j ∈ Finset.Icc 1 58,
      Valued.v (triangularNormPerturbation59 K f j) ≤
        WithZero.exp (-60 : ℤ) := by
  have hnormFormula := norm_aeval_triangularProduct 59
    (LambdaField59 K) (lambdaLocalPrimitiveRoot59 K) (twistedLambda59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K) (twistedLambda59_not_pow K)
    f 58 (by norm_num) (by norm_num)
  change Algebra.norm (LambdaField59 K)
      (aeval (twistedLambdaRoot59 K) (triangularProduct f 58)) =
    ∏ j ∈ Finset.Icc 1 58,
      (1 + triangularNormPerturbation59 K f j) at hnormFormula
  rw [hnormFormula] at hnorm
  exact triangularNormPerturbations59_mem_U60_of_product_mem_U59 K f hf hnorm

end Fermat.FiftyNine.Conservation.TriangularNormSeparation59
