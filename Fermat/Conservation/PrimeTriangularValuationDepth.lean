/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Valuation depth in triangular Kummer factorization

This is the valuation-native form of the quadratic contraction.  It avoids
passing through a real-valued norm: triangular elimination preserves the
input depth on every positive coefficient, while every coefficient above
the installed range has twice the depth.  The exact `X^p` quotient therefore
inherits doubled depth coefficient by coefficient.
-/
import Fermat.Conservation.PrimeTriangularUnitFactorization
import Mathlib.Tactic

open scoped WithZero
open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeTriangularValuationDepth

open PrimeTriangularUnitFactorization

variable {F : Type*} [Field F] [Valued F ℤᵐ⁰]

private theorem exp_neg_two_mul_le_exp_neg (s : ℕ) :
    WithZero.exp (-((2 * s : ℕ) : ℤ)) ≤ WithZero.exp (-(s : ℤ)) := by
  rw [WithZero.exp_le_exp]
  omega

private theorem exp_neg_mul_self (s : ℕ) :
    WithZero.exp (-(s : ℤ)) * WithZero.exp (-(s : ℤ)) =
      WithZero.exp (-((2 * s : ℕ) : ℤ)) := by
  rw [← WithZero.exp_add, WithZero.exp_inj]
  push_cast
  ring

/-- At every stage, all positive coefficients retain their input depth and
all coefficients above the installed range acquire twice that depth. -/
theorem triangularProduct_coefficient_depth
    (f : F[X]) (s : ℕ)
    (hf : ∀ k : ℕ, 0 < k →
      Valued.v (f.coeff k) ≤ WithZero.exp (-(s : ℤ))) :
    ∀ n : ℕ,
      (∀ k : ℕ, 0 < k →
        Valued.v ((triangularProduct f n).coeff k) ≤
          WithZero.exp (-(s : ℤ))) ∧
      (∀ k : ℕ, n < k →
        Valued.v ((triangularProduct f n).coeff k) ≤
          WithZero.exp (-((2 * s : ℕ) : ℤ))) := by
  intro n
  induction n with
  | zero =>
      constructor <;> intro k hk
      · have hk0 : k ≠ 0 := Nat.ne_of_gt hk
        simp [triangularProduct_zero, coeff_one, hk0]
      · have hk0 : k ≠ 0 := Nat.ne_of_gt hk
        simp [triangularProduct_zero, coeff_one, hk0]
  | succ n ih =>
      let c : F :=
        f.coeff (n + 1) - (triangularProduct f n).coeff (n + 1)
      have hc : Valued.v c ≤ WithZero.exp (-(s : ℤ)) := by
        apply (Valued.v : Valuation F ℤᵐ⁰).map_sub_le
        · exact hf (n + 1) (by omega)
        · exact (ih.2 (n + 1) (by omega)).trans
            (exp_neg_two_mul_le_exp_neg s)
      have hhigh : ∀ k : ℕ, n + 1 < k →
          Valued.v ((triangularProduct f (n + 1)).coeff k) ≤
            WithZero.exp (-((2 * s : ℕ) : ℤ)) := by
        intro k hk
        rw [triangularProduct_succ, mul_add, mul_one, coeff_add]
        rw [← mul_assoc, coeff_mul_X_pow']
        simp only [if_pos (by omega : n + 1 ≤ k), coeff_mul_C]
        apply (Valued.v : Valuation F ℤᵐ⁰).map_add_le
        · exact ih.2 k (by omega)
        · rw [map_mul]
          calc
            Valued.v ((triangularProduct f n).coeff (k - (n + 1))) *
                  Valued.v c ≤
                WithZero.exp (-(s : ℤ)) *
                  WithZero.exp (-(s : ℤ)) := by
              exact mul_le_mul (ih.1 (k - (n + 1)) (by omega)) hc bot_le bot_le
            _ = WithZero.exp (-((2 * s : ℕ) : ℤ)) :=
              exp_neg_mul_self s
      constructor
      · intro k hk
        rcases lt_trichotomy k (n + 1) with hlt | heq | hgt
        · rw [triangularProduct_coeff_lt_succ f n k hlt]
          exact ih.1 k hk
        · subst k
          rw [triangularProduct_coeff_succ]
          exact hf (n + 1) (by omega)
        · exact (hhigh k hgt).trans (exp_neg_two_mul_le_exp_neg s)
      · exact hhigh

/-- Coefficients of the exact `X^p` quotient inherit any common bound on
the coefficients of the triangular product above degree `p - 1`. -/
theorem remainder_coeff_valuation_le
    (f g : F[X]) (p : ℕ) (hp : 0 < p)
    (hfdeg : f.natDegree < p)
    (heq : f = triangularProduct f (p - 1) + X ^ p * g)
    (bound : ℤᵐ⁰)
    (hprod : ∀ n : ℕ, p - 1 < n →
      Valued.v ((triangularProduct f (p - 1)).coeff n) ≤ bound) :
    ∀ k : ℕ, Valued.v (g.coeff k) ≤ bound := by
  intro k
  have hfzero : f.coeff (k + p) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hcoeff := congrArg (fun q : F[X] => q.coeff (k + p)) heq
  rw [hfzero, coeff_add, coeff_X_pow_mul] at hcoeff
  have hg : g.coeff k = -(triangularProduct f (p - 1)).coeff (k + p) := by
    linear_combination -hcoeff
  rw [hg, (Valued.v : Valuation F ℤᵐ⁰).map_neg]
  exact hprod (k + p) (by omega)

/-- The quotient in the exact triangular remainder has doubled coefficient
depth.  This is the generic finite-amplifier step used at `p = 59`. -/
theorem exists_triangular_remainder_coefficient_depth_double
    (f : F[X]) (hf0 : f.coeff 0 = 1)
    (p : ℕ) (hp : 0 < p) (hfdeg : f.natDegree < p)
    (s : ℕ)
    (hf : ∀ k : ℕ, 0 < k →
      Valued.v (f.coeff k) ≤ WithZero.exp (-(s : ℤ))) :
    ∃ g : F[X],
      f = triangularProduct f (p - 1) + X ^ p * g ∧
      ∀ k : ℕ, Valued.v (g.coeff k) ≤
        WithZero.exp (-((2 * s : ℕ) : ℤ)) := by
  obtain ⟨g, hg⟩ := exists_triangular_remainder f hf0 p
  refine ⟨g, hg, ?_⟩
  exact remainder_coeff_valuation_le f g p hp hfdeg hg _
    (triangularProduct_coefficient_depth f s hf (p - 1)).2

end Fermat.Conservation.PrimeTriangularValuationDepth
