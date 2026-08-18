/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Finite triangular factorization modulo `X^p`

A polynomial with nonzero constant coefficient is factored, through degree
`p - 1`, into elementary factors `1 + c_j X^j`.  The construction is a
finite recursion on coefficients, not an enumeration of the exponent.

The exact remainder is divisible by `X^p`.  Therefore evaluation at an
element satisfying `alpha^p = a` turns it into an additive multiple of `a`;
when the explicit base product is nonzero, this becomes one multiplicative
principal factor `1 + a*y`.
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

open Polynomial

noncomputable section

namespace Fermat.Conservation.PrimeTriangularUnitFactorization

variable {F : Type*} [Field F]

/-- The successive product which matches the first `n` nonconstant
coefficients of `f`, assuming `f.coeff 0 = 1`. -/
def triangularProduct (f : F[X]) : ℕ → F[X]
  | 0 => 1
  | n + 1 =>
      let q := triangularProduct f n
      let c := f.coeff (n + 1) - q.coeff (n + 1)
      q * (1 + C c * X ^ (n + 1))

@[simp]
theorem triangularProduct_zero (f : F[X]) :
    triangularProduct f 0 = 1 := rfl

theorem triangularProduct_succ (f : F[X]) (n : ℕ) :
    triangularProduct f (n + 1) =
      triangularProduct f n *
        (1 + C (f.coeff (n + 1) -
          (triangularProduct f n).coeff (n + 1)) * X ^ (n + 1)) :=
  rfl

/-- The coefficient installed at the `j`-th triangular step. The value at
zero is immaterial because products only use positive indices. -/
def triangularCoefficient (f : F[X]) (j : ℕ) : F :=
  f.coeff j - (triangularProduct f (j - 1)).coeff j

theorem triangularCoefficient_succ (f : F[X]) (n : ℕ) :
    triangularCoefficient f (n + 1) =
      f.coeff (n + 1) -
        (triangularProduct f n).coeff (n + 1) := by
  simp [triangularCoefficient]

/-- The recursive polynomial is literally the product of the elementary
triangular factors installed so far. -/
theorem triangularProduct_eq_prod (f : F[X]) (n : ℕ) :
    triangularProduct f n =
      ∏ j ∈ Finset.Icc 1 n,
        (1 + C (triangularCoefficient f j) * X ^ j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
      rw [← ih, triangularProduct_succ, triangularCoefficient_succ]

@[simp]
theorem triangularProduct_coeff_zero (f : F[X]) (n : ℕ) :
    (triangularProduct f n).coeff 0 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [triangularProduct_succ, mul_add, mul_one, coeff_add]
      rw [← mul_assoc, coeff_mul_X_pow']
      simp [ih]

theorem triangularProduct_coeff_lt_succ (f : F[X]) (n k : ℕ)
    (hk : k < n + 1) :
    (triangularProduct f (n + 1)).coeff k =
      (triangularProduct f n).coeff k := by
  rw [triangularProduct_succ, mul_add, mul_one, coeff_add]
  rw [← mul_assoc, coeff_mul_X_pow']
  simp [Nat.not_le_of_lt hk]

theorem triangularProduct_coeff_succ (f : F[X]) (n : ℕ) :
    (triangularProduct f (n + 1)).coeff (n + 1) =
      f.coeff (n + 1) := by
  rw [triangularProduct_succ, mul_add, mul_one, coeff_add]
  rw [← mul_assoc]
  have hshift :
      ((triangularProduct f n *
          C (f.coeff (n + 1) -
            (triangularProduct f n).coeff (n + 1))) *
        X ^ (n + 1)).coeff (n + 1) =
      (triangularProduct f n *
          C (f.coeff (n + 1) -
            (triangularProduct f n).coeff (n + 1))).coeff 0 := by
    simpa using coeff_mul_X_pow
      (triangularProduct f n *
        C (f.coeff (n + 1) -
          (triangularProduct f n).coeff (n + 1))) (n + 1) 0
  rw [hshift]
  rw [coeff_mul_C, triangularProduct_coeff_zero]
  ring

/-- After `n` stages the constant coefficient and all coefficients through
degree `n` agree with the normalized target. -/
theorem triangularProduct_coeff_eq
    (f : F[X]) (hf0 : f.coeff 0 = 1) (n k : ℕ) (hk : k ≤ n) :
    (triangularProduct f n).coeff k = f.coeff k := by
  induction n with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simpa using hf0.symm
  | succ n ih =>
      rcases lt_or_eq_of_le hk with hlt | rfl
      · rw [triangularProduct_coeff_lt_succ f n k hlt]
        exact ih (Nat.le_of_lt_succ hlt)
      · exact triangularProduct_coeff_succ f n

/-- The normalized target differs from its triangular elementary-factor
product by an exact multiple of `X^p`. -/
theorem X_pow_dvd_sub_triangularProduct
    (f : F[X]) (hf0 : f.coeff 0 = 1) (p : ℕ) :
    X ^ p ∣ f - triangularProduct f (p - 1) := by
  rw [X_pow_dvd_iff]
  intro d hd
  rw [coeff_sub]
  by_cases hp0 : p = 0
  · omega
  · have hdpred : d ≤ p - 1 := by omega
    rw [triangularProduct_coeff_eq f hf0 (p - 1) d hdpred]
    exact sub_self _

/-- Exact remainder form of the triangular factorization. -/
theorem exists_triangular_remainder
    (f : F[X]) (hf0 : f.coeff 0 = 1) (p : ℕ) :
    ∃ g : F[X],
      f = triangularProduct f (p - 1) + X ^ p * g := by
  obtain ⟨g, hg⟩ := X_pow_dvd_sub_triangularProduct f hf0 p
  refine ⟨g, ?_⟩
  rw [← hg]
  ring

/-- Normalize a polynomial with nonzero constant coefficient to constant
coefficient one. -/
def normalizeConstant (f : F[X]) : F[X] :=
  C (f.coeff 0)⁻¹ * f

theorem normalizeConstant_coeff_zero (f : F[X]) (hf0 : f.coeff 0 ≠ 0) :
    (normalizeConstant f).coeff 0 = 1 := by
  rw [normalizeConstant, coeff_C_mul]
  exact inv_mul_cancel₀ hf0

theorem C_coeff_zero_mul_normalizeConstant
    (f : F[X]) (hf0 : f.coeff 0 ≠ 0) :
    C (f.coeff 0) * normalizeConstant f = f := by
  rw [normalizeConstant, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ hf0, C_1, one_mul]

/-- Unnormalized triangular factorization with an exact `X^p` remainder. -/
theorem exists_scaled_triangular_remainder
    (f : F[X]) (hf0 : f.coeff 0 ≠ 0) (p : ℕ) :
    ∃ g : F[X],
      f =
        C (f.coeff 0) *
          (∏ j ∈ Finset.Icc 1 (p - 1),
            (1 + C (triangularCoefficient (normalizeConstant f) j) * X ^ j)) +
        X ^ p * g := by
  obtain ⟨g, hg⟩ := exists_triangular_remainder
    (normalizeConstant f) (normalizeConstant_coeff_zero f hf0) p
  refine ⟨C (f.coeff 0) * g, ?_⟩
  calc
    f = C (f.coeff 0) * normalizeConstant f :=
      (C_coeff_zero_mul_normalizeConstant f hf0).symm
    _ = C (f.coeff 0) *
        (triangularProduct (normalizeConstant f) (p - 1) + X ^ p * g) := by
      exact congrArg (fun q : F[X] => C (f.coeff 0) * q) hg
    _ = C (f.coeff 0) * triangularProduct (normalizeConstant f) (p - 1) +
        X ^ p * (C (f.coeff 0) * g) := by ring
    _ = C (f.coeff 0) *
          (∏ j ∈ Finset.Icc 1 (p - 1),
            (1 + C (triangularCoefficient (normalizeConstant f) j) * X ^ j)) +
        X ^ p * (C (f.coeff 0) * g) := by
      rw [triangularProduct_eq_prod]

/-- Evaluating the triangular factorization at a `p`-th root turns the
`X^p` remainder into an exact multiple of the base-field element `a`. -/
theorem exists_aeval_scaled_triangular_remainder
    {E : Type*} [Field E] [Algebra F E]
    (f : F[X]) (hf0 : f.coeff 0 ≠ 0) (p : ℕ)
    (alpha : E) (a : F) (halpha : alpha ^ p = algebraMap F E a) :
    ∃ delta : E,
      aeval alpha f =
        algebraMap F E (f.coeff 0) *
          (∏ j ∈ Finset.Icc 1 (p - 1),
            (1 + algebraMap F E
              (triangularCoefficient (normalizeConstant f) j) * alpha ^ j)) +
        algebraMap F E a * delta := by
  obtain ⟨g, hg⟩ := exists_scaled_triangular_remainder f hf0 p
  refine ⟨aeval alpha g, ?_⟩
  have heval := congrArg (fun q : F[X] => aeval alpha q) hg
  simpa only [map_add, map_mul, map_pow, map_prod, map_one, aeval_C, aeval_X,
    halpha] using heval

/-- If the explicit elementary-factor product is nonzero, the additive
`a`-remainder can be absorbed into one multiplicative principal factor. -/
theorem exists_aeval_multiplicative_remainder
    {E : Type*} [Field E] [Algebra F E]
    (f : F[X]) (hf0 : f.coeff 0 ≠ 0) (p : ℕ)
    (alpha : E) (a : F) (halpha : alpha ^ p = algebraMap F E a)
    (hbase :
      algebraMap F E (f.coeff 0) *
        (∏ j ∈ Finset.Icc 1 (p - 1),
          (1 + algebraMap F E
            (triangularCoefficient (normalizeConstant f) j) * alpha ^ j)) ≠ 0) :
    ∃ y : E,
      aeval alpha f =
        (algebraMap F E (f.coeff 0) *
          (∏ j ∈ Finset.Icc 1 (p - 1),
            (1 + algebraMap F E
              (triangularCoefficient (normalizeConstant f) j) * alpha ^ j))) *
        (1 + algebraMap F E a * y) := by
  obtain ⟨delta, hdelta⟩ :=
    exists_aeval_scaled_triangular_remainder f hf0 p alpha a halpha
  let base : E :=
    algebraMap F E (f.coeff 0) *
      (∏ j ∈ Finset.Icc 1 (p - 1),
        (1 + algebraMap F E
          (triangularCoefficient (normalizeConstant f) j) * alpha ^ j))
  refine ⟨delta / base, ?_⟩
  change aeval alpha f = base * (1 + algebraMap F E a * (delta / base))
  rw [hdelta]
  change base + algebraMap F E a * delta =
    base * (1 + algebraMap F E a * (delta / base))
  field_simp [base, hbase]

end Fermat.Conservation.PrimeTriangularUnitFactorization
