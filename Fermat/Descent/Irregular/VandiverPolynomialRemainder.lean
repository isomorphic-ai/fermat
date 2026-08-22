import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# Vandiver's integer polynomial remainder decomposition

This file isolates the elementary polynomial division used in Vandiver's
passage from a relation at a primitive `p`-th root of unity to the
coefficient congruences surrounding equation (3d).

If an integer polynomial `A` vanishes at a primitive `p`-th root, its
minimal polynomial `Φₚ` divides `A`.  Writing the quotient modulo `X-1`
then gives

`A = (X^p - 1) * V + C b * Φₚ`

with `A(1) = p*b`.  Consequently `p ∣ A(1)`, and the stronger hypothesis
`p² ∣ A(1)` forces `p ∣ b`.

The argument is entirely over `ℤ`; no power-series logarithm or desired
derivative conclusion is included among its hypotheses.
-/

namespace Fermat.Irregular.VandiverPolynomialRemainder

open Polynomial

/-- An integer polynomial which vanishes at a primitive `p`-th root is
divisible by the integer cyclotomic polynomial `Φₚ`. -/
theorem cyclotomic_dvd_of_aeval_primitiveRoot
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (A : ℤ[X]) (hA : aeval ζ A = 0) :
    cyclotomic p ℤ ∣ A := by
  rw [cyclotomic_eq_minpoly hζ hp.pos]
  exact minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hp.pos) hA

/-- Vandiver's integer polynomial remainder decomposition.

The constant `b` is the value at `1` of the quotient `A / Φₚ`; the second
conclusion characterizes it without using polynomial or integer division:
`A(1) = p*b`. -/
theorem exists_polynomial_remainder_decomposition
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (A : ℤ[X]) (hA : aeval ζ A = 0) :
    ∃ (V : ℤ[X]) (b : ℤ),
      A = (X ^ p - 1) * V + C b * cyclotomic p ℤ ∧
      A.eval 1 = (p : ℤ) * b := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hB⟩ :=
    cyclotomic_dvd_of_aeval_primitiveRoot hp hζ A hA
  let b : ℤ := B.eval 1
  obtain ⟨V, hV⟩ :=
    (X_sub_C_dvd_sub_C_eval (p := B) (a := (1 : ℤ)))
  refine ⟨V, b, ?_, ?_⟩
  · calc
      A = cyclotomic p ℤ * B := hB
      _ = cyclotomic p ℤ *
          ((X - C (1 : ℤ)) * V + C b) := by
            rw [← hV]
            simp only [b]
            ring
      _ = (X ^ p - 1) * V + C b * cyclotomic p ℤ := by
            rw [show C (1 : ℤ) = (1 : ℤ[X]) by simp,
              mul_add, ← mul_assoc,
              cyclotomic_prime_mul_X_sub_one ℤ p]
            ring
  · rw [hB, eval_mul, eval_one_cyclotomic_prime]

/-- The first numerical consequence of the remainder decomposition:
`p` divides the value of `A` at `1`. -/
theorem prime_dvd_eval_one_of_aeval_primitiveRoot
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (A : ℤ[X]) (hA : aeval ζ A = 0) :
    (p : ℤ) ∣ A.eval 1 := by
  obtain ⟨_, b, _, heval⟩ :=
    exists_polynomial_remainder_decomposition hp hζ A hA
  exact ⟨b, heval⟩

/-- If `A(1)=p*b` and `p²` divides `A(1)`, then `p` divides the
cyclotomic remainder coefficient `b`. -/
theorem prime_dvd_remainder_of_square_dvd_eval
    {p : ℕ} (hp : p.Prime) {A : ℤ[X]} {b : ℤ}
    (heval : A.eval 1 = (p : ℤ) * b)
    (hsquare : (p : ℤ) ^ 2 ∣ A.eval 1) :
    (p : ℤ) ∣ b := by
  obtain ⟨c, hc⟩ := hsquare
  refine ⟨c, ?_⟩
  apply mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)
  calc
    (p : ℤ) * b = A.eval 1 := heval.symm
    _ = (p : ℤ) ^ 2 * c := hc
    _ = (p : ℤ) * ((p : ℤ) * c) := by ring

/-- Combined form used when equation (3d) already supplies the square
divisibility of `A(1)`. -/
theorem exists_polynomial_remainder_decomposition_of_square_dvd_eval
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (A : ℤ[X]) (hA : aeval ζ A = 0)
    (hsquare : (p : ℤ) ^ 2 ∣ A.eval 1) :
    ∃ (V : ℤ[X]) (b : ℤ),
      A = (X ^ p - 1) * V + C b * cyclotomic p ℤ ∧
      A.eval 1 = (p : ℤ) * b ∧
      (p : ℤ) ∣ b := by
  obtain ⟨V, b, hdecomp, heval⟩ :=
    exists_polynomial_remainder_decomposition hp hζ A hA
  exact ⟨V, b, hdecomp, heval,
    prime_dvd_remainder_of_square_dvd_eval hp heval hsquare⟩

end Fermat.Irregular.VandiverPolynomialRemainder
