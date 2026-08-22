/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The critical-depth gap for Kummer monomial norms at 59

The norm of `1 + c * alpha^j`, for `0 < j < 59`, differs from one by
`c^59 * (60*lambda)^j`.  Its lambda depth is congruent to `-j` modulo
59, so it cannot stop at depth 59: entering `U_59` forces it into `U_60`.

This proves the desired norm-filtration silence for each individual
nonconstant power-basis perturbation.  Passing from these factors to an
arbitrary extension unit still requires the separate integral normal-form
or ramification-filtration theorem.
-/
import Fermat.Experiments.Conservation.PrimeKummerExplicitNorm
import Fermat.Exponents.FiftyNine.Conservation.TwistedLambdaNormCorrection59

open scoped NumberField WithZero

noncomputable section

namespace Fermat.FiftyNine.Conservation.ExplicitNormResidue59

open Fermat.Conservation.PrimeKummerExplicitNorm
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The generic selected root is definitionally the existing twisted-lambda
root at 59. -/
theorem selectedTwistedKummerRoot59_eq_twistedLambdaRoot59 :
    selectedKummerRoot 59 (LambdaField59 K) (twistedLambda59 K) =
      twistedLambdaRoot59 K :=
  rfl

/-- Exact actual field norm of a single nonconstant power-basis
perturbation in the twisted-lambda extension. -/
theorem norm_one_add_twistedLambdaRootPow59
    (c : LambdaField59 K) (j : ℕ) (hj0 : 0 < j) (hj59 : j < 59) :
    Algebra.norm (LambdaField59 K)
        (1 + algebraMap (LambdaField59 K)
            (twistedLambdaKummerExtension59 K) c *
          twistedLambdaRoot59 K ^ j) =
      1 + c ^ 59 * twistedLambda59 K ^ j := by
  exact norm_one_add_smul_root_pow 59 (LambdaField59 K)
    (lambdaLocalPrimitiveRoot59 K) (twistedLambda59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)
    (twistedLambda59_not_pow K) c j hj0 hj59 (by norm_num)

/-- The valuation depth of a nonconstant Kummer monomial is congruent to
`-j` modulo 59. Hence it cannot stop at the critical depth 59. -/
theorem monomialDepthGap59
    (c : LambdaField59 K) (j : ℕ) (hj0 : 0 < j) (hj59 : j < 59)
    (hcritical :
      Valued.v (c ^ 59 * twistedLambda59 K ^ j) ≤
        WithZero.exp (-59 : ℤ)) :
    Valued.v (c ^ 59 * twistedLambda59 K ^ j) ≤
      WithZero.exp (-60 : ℤ) := by
  rw [map_mul, map_pow, map_pow, twistedLambda59_valuation] at hcritical ⊢
  cases hvc : Valued.v c with
  | zero => simp
  | coe z =>
      let k : ℤ := Multiplicative.toAdd z
      have hz : (↑z : WithZero (Multiplicative ℤ)) =
          WithZero.exp k := by rfl
      rw [hvc, hz] at hcritical
      rw [hz]
      simp only [← WithZero.exp_nsmul, ← WithZero.exp_add,
        WithZero.exp_le_exp] at hcritical ⊢
      simp only [nsmul_eq_mul] at hcritical ⊢
      norm_num at hcritical ⊢
      have hne : 59 * k - (j : ℤ) ≠ -59 := by
        intro heq
        have hdvd : (59 : ℤ) ∣ (j : ℤ) := by
          use k + 1
          omega
        have hjdvd : (59 : ℕ) ∣ j := by exact_mod_cast hdvd
        have h59le : 59 ≤ j := Nat.le_of_dvd hj0 hjdvd
        omega
      omega

/-- For every one-monomial power-basis perturbation, if its actual field
norm enters `U_59`, then it already lies in `U_60`. -/
theorem norm_one_add_twistedLambdaRootPow59_depthGap
    (c : LambdaField59 K) (j : ℕ) (hj0 : 0 < j) (hj59 : j < 59)
    (hcritical :
      Valued.v
          (Algebra.norm (LambdaField59 K)
              (1 + algebraMap (LambdaField59 K)
                  (twistedLambdaKummerExtension59 K) c *
                twistedLambdaRoot59 K ^ j) - 1) ≤
        WithZero.exp (-59 : ℤ)) :
    Valued.v
        (Algebra.norm (LambdaField59 K)
            (1 + algebraMap (LambdaField59 K)
                (twistedLambdaKummerExtension59 K) c *
              twistedLambdaRoot59 K ^ j) - 1) ≤
      WithZero.exp (-60 : ℤ) := by
  rw [norm_one_add_twistedLambdaRootPow59 K c j hj0 hj59,
    add_sub_cancel_left] at hcritical ⊢
  exact monomialDepthGap59 K c j hj0 hj59 hcritical

end Fermat.FiftyNine.Conservation.ExplicitNormResidue59
