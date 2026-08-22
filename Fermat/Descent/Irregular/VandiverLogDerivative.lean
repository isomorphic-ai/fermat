import Mathlib.NumberTheory.Bernoulli

/-!
# Vandiver's logarithmic derivative

The analytic calculation in Vandiver's 1929 Lemma 2 can be carried out
without convergence arguments.  The exponential generating function
`bernoulli'PowerSeries ℚ` is

`X * exp X / (exp X - 1)`.

Consequently, after replacing `X` by `r * X`, subtracting the original
series, and cancelling one factor of `X`, one obtains the regularized
logarithmic derivative

`r * exp (rX) / (exp (rX) - 1) - exp X / (exp X - 1)`.

The denominators in this display have zero constant coefficient, so the
identity is stated below in cross-multiplied form.  Its coefficients give
Vandiver's displayed formula on p. 619:

`D^(2*k-1) L_r(0) = B_(2*k) / (2*k) * (r^(2*k) - 1)`.

Here `formalDerivativeAtZero n f = n! * coeff n f`; it is the value at zero
of the `n`-th formal derivative.  This module is purely algebraic and uses no
analytic axioms.
-/

namespace Fermat.Irregular.VandiverLogDerivative

open PowerSeries

noncomputable section

/-- The value at zero of the `n`-th formal derivative of a power series. -/
def formalDerivativeAtZero (n : ℕ) (f : PowerSeries ℚ) : ℚ :=
  (n.factorial : ℚ) * PowerSeries.coeff n f

/-- The regularized logarithmic derivative used by Vandiver.  It is the
tail, or division by `X`, of the difference between the rescaled and
unscaled Bernoulli generating series. -/
def vandiverLogDerivative (r : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n ↦
    PowerSeries.coeff (n + 1)
      (PowerSeries.rescale r (bernoulli'PowerSeries ℚ) -
        bernoulli'PowerSeries ℚ)

/-- The defining difference has zero constant coefficient, and its exact
quotient by `X` is `vandiverLogDerivative`. -/
theorem bernoulliDifference_eq_X_mul (r : ℚ) :
    PowerSeries.rescale r (bernoulli'PowerSeries ℚ) -
        bernoulli'PowerSeries ℚ =
      PowerSeries.X * vandiverLogDerivative r := by
  ext (_ | n)
  · rw [map_sub, PowerSeries.coeff_rescale]
    norm_num [bernoulli'PowerSeries]
  · simp [vandiverLogDerivative]

/-- Rescaling the Bernoulli generating-function identity.  The extra
constant `r` is the chain-rule factor in the logarithmic derivative. -/
theorem rescale_bernoulli_mul_exp_sub_one (r : ℚ) :
    PowerSeries.rescale r (bernoulli'PowerSeries ℚ) *
        (PowerSeries.rescale r (PowerSeries.exp ℚ) - 1) =
      PowerSeries.C r * PowerSeries.X *
        PowerSeries.rescale r (PowerSeries.exp ℚ) := by
  have h := congrArg (PowerSeries.rescale r)
    (bernoulli'PowerSeries_mul_exp_sub_one ℚ)
  simpa [PowerSeries.rescale_X, mul_assoc] using h

/-- Cross-multiplied form of

`L_r = r * exp (rX) / (exp (rX) - 1) - exp X / (exp X - 1)`.

This proves that `vandiverLogDerivative` is the historical logarithmic
derivative, despite both displayed fractions having singular denominators
before their difference is regularized. -/
theorem vandiverLogDerivative_mul_exp_factors (r : ℚ) :
    vandiverLogDerivative r *
        (PowerSeries.rescale r (PowerSeries.exp ℚ) - 1) *
        (PowerSeries.exp ℚ - 1) =
      PowerSeries.C r * PowerSeries.rescale r (PowerSeries.exp ℚ) *
          (PowerSeries.exp ℚ - 1) -
        PowerSeries.exp ℚ *
          (PowerSeries.rescale r (PowerSeries.exp ℚ) - 1) := by
  apply PowerSeries.X_mul_injective
  calc
    PowerSeries.X *
        (vandiverLogDerivative r *
          (PowerSeries.rescale r (PowerSeries.exp ℚ) - 1) *
          (PowerSeries.exp ℚ - 1)) =
        (PowerSeries.rescale r (bernoulli'PowerSeries ℚ) -
          bernoulli'PowerSeries ℚ) *
          (PowerSeries.rescale r (PowerSeries.exp ℚ) - 1) *
          (PowerSeries.exp ℚ - 1) := by
            rw [bernoulliDifference_eq_X_mul]
            ring
    _ =
        (PowerSeries.rescale r (bernoulli'PowerSeries ℚ) *
            (PowerSeries.rescale r (PowerSeries.exp ℚ) - 1)) *
            (PowerSeries.exp ℚ - 1) -
          (bernoulli'PowerSeries ℚ * (PowerSeries.exp ℚ - 1)) *
            (PowerSeries.rescale r (PowerSeries.exp ℚ) - 1) := by ring
    _ =
        (PowerSeries.C r * PowerSeries.X *
            PowerSeries.rescale r (PowerSeries.exp ℚ)) *
            (PowerSeries.exp ℚ - 1) -
          (PowerSeries.X * PowerSeries.exp ℚ) *
            (PowerSeries.rescale r (PowerSeries.exp ℚ) - 1) := by
              rw [rescale_bernoulli_mul_exp_sub_one,
                bernoulli'PowerSeries_mul_exp_sub_one]
    _ = PowerSeries.X *
        (PowerSeries.C r * PowerSeries.rescale r (PowerSeries.exp ℚ) *
            (PowerSeries.exp ℚ - 1) -
          PowerSeries.exp ℚ *
            (PowerSeries.rescale r (PowerSeries.exp ℚ) - 1)) := by ring

/-- Coefficients of the regularized logarithmic derivative. -/
@[simp]
theorem coeff_vandiverLogDerivative (r : ℚ) (n : ℕ) :
    PowerSeries.coeff n (vandiverLogDerivative r) =
      (r ^ (n + 1) - 1) * bernoulli' (n + 1) /
        (n + 1).factorial := by
  simp [vandiverLogDerivative, bernoulli'PowerSeries]
  ring

/-- Vandiver's coefficient formula before specializing to an even
Bernoulli index. -/
theorem formalDerivativeAtZero_vandiverLogDerivative (r : ℚ) (n : ℕ) :
    formalDerivativeAtZero n (vandiverLogDerivative r) =
      bernoulli' (n + 1) / (n + 1) * (r ^ (n + 1) - 1) := by
  rw [formalDerivativeAtZero, coeff_vandiverLogDerivative,
    Nat.factorial_succ]
  push_cast
  field_simp

/-- Formal chain rule at zero for the substitution `X ↦ r * X`.  This is
Vandiver's scaling identity (3e). -/
theorem formalDerivativeAtZero_rescale
    (r : ℚ) (f : PowerSeries ℚ) (n : ℕ) :
    formalDerivativeAtZero n (PowerSeries.rescale r f) =
      r ^ n * formalDerivativeAtZero n f := by
  simp only [formalDerivativeAtZero, PowerSeries.coeff_rescale]
  ring

/-- Vandiver's displayed logarithmic-derivative formula, in Mathlib's
modern Bernoulli convention.  The historical positive number `B_k` is the
absolute value of the even number `bernoulli (2*k)`; the sign in his display
accounts for that convention change. -/
theorem even_formalDerivativeAtZero_vandiverLogDerivative
    (r : ℚ) (k : ℕ) (hk : 0 < k) :
    formalDerivativeAtZero (2 * k - 1) (vandiverLogDerivative r) =
      bernoulli (2 * k) / (2 * k) * (r ^ (2 * k) - 1) := by
  rw [formalDerivativeAtZero_vandiverLogDerivative]
  have hsucc : 2 * k - 1 + 1 = 2 * k := by omega
  rw [hsucc, bernoulli'_eq_bernoulli]
  simp only [Even.neg_one_pow (even_two_mul k), one_mul]
  norm_num [Nat.cast_sub (by omega : 1 ≤ 2 * k)]

end

end Fermat.Irregular.VandiverLogDerivative
