/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Quantitative bounds for triangular Kummer factorization

The finite triangular factorization is contractive over an ultrametric
field.  If all nonconstant coefficients have norm at most `q ≤ 1`, every
installed elementary coefficient has the same bound, while the exact
`X^p` remainder improves to `q²`.  These statements are prime-parametric
and avoid expanding a determinant or enumerating coefficients.
-/
import Fermat.Experiments.Conservation.PrimeTriangularUnitFactorization
import Fermat.Experiments.Conservation.NonarchimedeanProductRemainder

open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeTriangularNormBounds

open PrimeTriangularUnitFactorization
open NonarchimedeanProductRemainder

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]

/-- If all nonconstant target coefficients have norm at most `q ≤ 1`,
then every coefficient installed by triangular factorization has the same
bound. -/
theorem triangularCoefficient_norm_le
    (f : F[X]) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hf : ∀ j : ℕ, 0 < j → ‖f.coeff j‖ ≤ q) :
    ∀ j : ℕ, 0 < j → ‖triangularCoefficient f j‖ ≤ q := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro hj
      let s := Finset.Icc 1 (j - 1)
      let x : ℕ → F[X] := fun k ↦
        C (triangularCoefficient f k) * X ^ k
      have hx : ∀ k ∈ s, (x k).supNorm ≤ q := by
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkj : k < j := by
          have hkle : k ≤ j - 1 := (Finset.mem_Icc.mp hk).2
          omega
        have hck := ih k hkj (by omega : 0 < k)
        simpa [x, C_mul_X_pow_eq_monomial] using hck
      have hprod :=
        (polynomial_prod_one_add_first_order_bound
          s x q hq0 hq1 hx).1
      have hprod' :
          (triangularProduct f (j - 1) - 1).supNorm ≤ q := by
        rw [triangularProduct_eq_prod f (j - 1)]
        exact hprod
      have hcoeffSub :
          ‖(triangularProduct f (j - 1) - 1).coeff j‖ ≤ q :=
        ((triangularProduct f (j - 1) - 1).le_supNorm j).trans hprod'
      have hcoeff :
          ‖(triangularProduct f (j - 1)).coeff j‖ ≤ q := by
        rw [coeff_sub, coeff_one, if_neg hj.ne'] at hcoeffSub
        simpa using hcoeffSub
      have hna := IsUltrametricDist.isNonarchimedean_norm
        (f.coeff j) (-(triangularProduct f (j - 1)).coeff j)
      rw [triangularCoefficient]
      exact (by
        simpa [sub_eq_add_neg] using
          hna.trans (max_le (hf j hj) (by simpa using hcoeff)))

/-- For a normalized polynomial of degree below `p`, the exact `X^p`
remainder left by triangular factorization has coefficient sup norm at most
the square of the common nonconstant-coefficient bound. -/
theorem sub_triangularProduct_supNorm_le_sq
    (f : F[X]) (hf0 : f.coeff 0 = 1)
    (p : ℕ) (hp : 0 < p) (hdeg : f.natDegree < p)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hf : ∀ j : ℕ, 0 < j → ‖f.coeff j‖ ≤ q) :
    (f - triangularProduct f (p - 1)).supNorm ≤ q ^ 2 := by
  let s := Finset.Icc 1 (p - 1)
  let x : ℕ → F[X] := fun k ↦
    C (triangularCoefficient f k) * X ^ k
  have hc := triangularCoefficient_norm_le f q hq0 hq1 hf
  have hx : ∀ k ∈ s, (x k).supNorm ≤ q := by
    intro k hk
    have hkpos : 0 < k := by
      have := (Finset.mem_Icc.mp hk).1
      omega
    simpa [x, C_mul_X_pow_eq_monomial] using hc k hkpos
  have hquadratic :=
    (polynomial_prod_one_add_first_order_bound s x q hq0 hq1 hx).2
  have hquadratic' :
      (triangularProduct f (p - 1) - 1 - s.sum x).supNorm ≤ q ^ 2 := by
    rw [triangularProduct_eq_prod f (p - 1)]
    exact hquadratic
  have hcoeff (i : ℕ) :
      ‖(f - triangularProduct f (p - 1)).coeff i‖ ≤ q ^ 2 := by
    by_cases hi : i < p
    · have hile : i ≤ p - 1 := by omega
      rw [coeff_sub, triangularProduct_coeff_eq f hf0 (p - 1) i hile,
        sub_self, norm_zero]
      exact sq_nonneg q
    · have hpi : p ≤ i := Nat.le_of_not_gt hi
      have hfi : f.coeff i = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg hpi)
      have hi0 : i ≠ 0 := by omega
      have hone : (1 : F[X]).coeff i = 0 := by
        rw [coeff_one, if_neg hi0]
      have hsum : (s.sum x).coeff i = 0 := by
        have haux (t : Finset ℕ) (ht : ∀ k ∈ t, k ≤ p - 1) :
            (t.sum x).coeff i = 0 := by
          induction t using Finset.induction_on with
          | empty => simp
          | @insert k t hkt ih =>
              rw [Finset.sum_insert hkt, coeff_add, ih]
              · have hkle := ht k (Finset.mem_insert_self k t)
                have hki : k ≠ i := by omega
                simp [C_mul_X_pow_eq_monomial, coeff_monomial, hki]
              · intro l hl
                exact ht l (Finset.mem_insert_of_mem hl)
        exact haux s (fun k hk ↦ (Finset.mem_Icc.mp hk).2)
      have hrem :=
        ((triangularProduct f (p - 1) - 1 - s.sum x).le_supNorm i).trans
          hquadratic'
      rw [coeff_sub, coeff_sub, hone, hsum, sub_zero, sub_zero] at hrem
      rw [coeff_sub, hfi, zero_sub, norm_neg]
      exact hrem
  obtain ⟨i, hi⟩ := (f - triangularProduct f (p - 1)).exists_eq_supNorm
  rw [hi]
  exact hcoeff i

/-- The quotient by `X^p` in the exact triangular remainder inherits the
quadratically improved coefficient bound. -/
theorem exists_triangular_remainder_supNorm_le_sq
    (f : F[X]) (hf0 : f.coeff 0 = 1)
    (p : ℕ) (hp : 0 < p) (hdeg : f.natDegree < p)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hf : ∀ j : ℕ, 0 < j → ‖f.coeff j‖ ≤ q) :
    ∃ g : F[X],
      f = triangularProduct f (p - 1) + X ^ p * g ∧
      g.supNorm ≤ q ^ 2 := by
  obtain ⟨g, hg⟩ := exists_triangular_remainder f hf0 p
  refine ⟨g, hg, ?_⟩
  have hsub := sub_triangularProduct_supNorm_le_sq
    f hf0 p hp hdeg q hq0 hq1 hf
  have heq : f - triangularProduct f (p - 1) = X ^ p * g := by
    calc
      f - triangularProduct f (p - 1) =
          (triangularProduct f (p - 1) + X ^ p * g) -
            triangularProduct f (p - 1) :=
        congrArg (fun z : F[X] ↦ z - triangularProduct f (p - 1)) hg
      _ = X ^ p * g := by ring
  rw [heq] at hsub
  have hmul : (X ^ p * g : F[X]).supNorm = g.supNorm := by
    change polynomialSupAbsoluteValue (X ^ p * g) = g.supNorm
    rw [map_mul, map_pow, polynomialSupAbsoluteValue_apply,
      polynomialSupAbsoluteValue_apply]
    simp
  rwa [hmul] at hsub

end Fermat.Conservation.PrimeTriangularNormBounds
