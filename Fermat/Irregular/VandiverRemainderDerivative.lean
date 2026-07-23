import Fermat.Irregular.VandiverPowerSeriesLog
import Fermat.Irregular.VandiverPolynomialRemainder
import Fermat.Irregular.Voronoi

/-!
# Derivatives of Vandiver's polynomial remainder

This file formalizes the high-derivative congruence on pages 619–620 of
Vandiver's argument.  Starting from the integer-polynomial decomposition

`A = (X^p - 1) * V + C (p*b₁) * Φₚ`,

we substitute `X = exp T`.  The `N`-th derivative at `T = 0` of the first
summand is an integer combination of

`(k+p)^N - k^N`,

which is divisible by `p²` when `p ∣ N`.  The derivative of the second
summand is

`p*b₁ * ∑ j < p, j^N`;

the power sum contributes its second factor of `p` when `p` is prime,
`N > 0`, and `(p-1) ∤ N`.

The resulting theorem is stated as a lower bound on the `p`-adic valuation
of the formal derivative.  No analytic exponential or differentiation is
used.
-/

namespace Fermat.Irregular.VandiverRemainderDerivative

open Polynomial PowerSeries
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.Voronoi

/-- The `N`-th formal derivative at zero of `exp(T)^k` is `k^N`. -/
theorem formalDerivativeAtZero_exp_pow (k N : ℕ) :
    formalDerivativeAtZero N (PowerSeries.exp ℚ ^ k) =
      (k : ℚ) ^ N := by
  rw [PowerSeries.exp_pow_eq_rescale_exp,
    formalDerivativeAtZero_rescale]
  simp [formalDerivativeAtZero, PowerSeries.coeff_exp]
  field_simp

/-- Substitute the formal exponential into an integer polynomial. -/
noncomputable def polynomialExp (P : ℤ[X]) : PowerSeries ℚ :=
  Polynomial.eval₂ (algebraMap ℤ (PowerSeries ℚ))
    (PowerSeries.exp ℚ) P

theorem polynomialExp_eq_sum (P : ℤ[X]) :
    polynomialExp P =
      ∑ k ∈ P.support,
        PowerSeries.C (P.coeff k : ℚ) * PowerSeries.exp ℚ ^ k := by
  rw [polynomialExp, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro k hk
  simp

/-- The derivative of a polynomial after exponential substitution is its
corresponding power moment. -/
theorem formalDerivativeAtZero_polynomialExp (P : ℤ[X]) (N : ℕ) :
    formalDerivativeAtZero N (polynomialExp P) =
      P.sum fun k a ↦ (a : ℚ) * (k : ℚ) ^ N := by
  rw [polynomialExp_eq_sum, Polynomial.sum_def,
    formalDerivativeAtZero_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_exp_pow]

theorem formalDerivativeAtZero_sub
    (N : ℕ) (f g : PowerSeries ℚ) :
    formalDerivativeAtZero N (f - g) =
      formalDerivativeAtZero N f - formalDerivativeAtZero N g := by
  simp [formalDerivativeAtZero]
  ring

theorem shiftedPolynomialExp_eq_sum (p : ℕ) (P : ℤ[X]) :
    (PowerSeries.exp ℚ ^ p - 1) * polynomialExp P =
      ∑ k ∈ P.support,
        PowerSeries.C (P.coeff k : ℚ) *
          (PowerSeries.exp ℚ ^ (k + p) -
            PowerSeries.exp ℚ ^ k) := by
  rw [polynomialExp_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    (PowerSeries.exp ℚ ^ p - 1) *
        (PowerSeries.C (P.coeff k : ℚ) * PowerSeries.exp ℚ ^ k) =
      PowerSeries.C (P.coeff k : ℚ) *
        (PowerSeries.exp ℚ ^ p * PowerSeries.exp ℚ ^ k -
          PowerSeries.exp ℚ ^ k) := by ring
    _ = PowerSeries.C (P.coeff k : ℚ) *
        (PowerSeries.exp ℚ ^ (k + p) -
          PowerSeries.exp ℚ ^ k) := by
      rw [← pow_add, add_comm]

theorem formalDerivativeAtZero_shiftedPolynomialExp
    (p : ℕ) (P : ℤ[X]) (N : ℕ) :
    formalDerivativeAtZero N
        ((PowerSeries.exp ℚ ^ p - 1) * polynomialExp P) =
      P.sum fun k a ↦
        (a : ℚ) * (((k + p : ℕ) : ℚ) ^ N - (k : ℚ) ^ N) := by
  rw [shiftedPolynomialExp_eq_sum, Polynomial.sum_def,
    formalDerivativeAtZero_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_sub,
    formalDerivativeAtZero_exp_pow,
    formalDerivativeAtZero_exp_pow]

theorem formalDerivativeAtZero_geomExp (p N : ℕ) :
    formalDerivativeAtZero N (geomExp p) =
      ∑ j ∈ Finset.range p, (j : ℚ) ^ N := by
  rw [geomExp, formalDerivativeAtZero_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [formalDerivativeAtZero_exp_pow]

/-- The integral moment attached to `(exp(T)^p - 1) * P(exp T)`. -/
def shiftedPolynomialMoment (p : ℕ) (P : ℤ[X]) (N : ℕ) : ℤ :=
  P.sum fun k a ↦
    a * ((((k + p : ℕ) : ℤ) ^ N) - (k : ℤ) ^ N)

theorem formalDerivativeAtZero_shiftedPolynomialExp_eq_intCast
    (p : ℕ) (P : ℤ[X]) (N : ℕ) :
    formalDerivativeAtZero N
        ((PowerSeries.exp ℚ ^ p - 1) * polynomialExp P) =
      (shiftedPolynomialMoment p P N : ℚ) := by
  rw [formalDerivativeAtZero_shiftedPolynomialExp]
  simp only [shiftedPolynomialMoment, Polynomial.sum_def]
  push_cast
  rfl

/-- The integral power sum arising from the substituted prime cyclotomic
polynomial. -/
def powerSumInt (p N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range p, (j : ℤ) ^ N

theorem formalDerivativeAtZero_geomExp_eq_intCast (p N : ℕ) :
    formalDerivativeAtZero N (geomExp p) =
      (powerSumInt p N : ℚ) := by
  rw [formalDerivativeAtZero_geomExp, powerSumInt]
  push_cast
  rfl

/-- If `p ∣ N`, translating an integer base by `p` does not change its
`N`-th power modulo `p²`. -/
theorem square_dvd_shifted_pow_sub
    {p N : ℕ} (hN : p ∣ N) (k : ℤ) :
    (p : ℤ) ^ 2 ∣ (k + p) ^ N - k ^ N := by
  obtain ⟨t, rfl⟩ := hN
  have hmod := add_multiple_pow_int_modEq_sq p k 1 (p * t)
  have hcorr :
      ((p * t : ℕ) : ℤ) * ((p : ℤ) * 1) * k ^ (p * t - 1) ≡
        0 [ZMOD (p : ℤ) ^ 2] := by
    rw [Int.modEq_iff_dvd]
    have hdiv : (p : ℤ) ^ 2 ∣
        ((p * t : ℕ) : ℤ) * ((p : ℤ) * 1) *
          k ^ (p * t - 1) := by
      refine ⟨(t : ℤ) * k ^ (p * t - 1), ?_⟩
      push_cast
      ring
    simpa only [zero_sub] using dvd_neg.mpr hdiv
  have hright :
      k ^ (p * t) +
          ((p * t : ℕ) : ℤ) * ((p : ℤ) * 1) * k ^ (p * t - 1) ≡
        k ^ (p * t) [ZMOD (p : ℤ) ^ 2] := by
    simpa using (Int.ModEq.refl (n := (p : ℤ) ^ 2)
      (k ^ (p * t))).add hcorr
  have hfinal :
      (k + (p : ℤ)) ^ (p * t) ≡ k ^ (p * t)
        [ZMOD (p : ℤ) ^ 2] := by
    simpa only [mul_one] using hmod.trans hright
  have hdvd := hfinal.dvd
  apply dvd_neg.mp
  simpa only [neg_sub] using hdvd

/-- The classical non-exceptional finite-field power-sum congruence. -/
theorem prime_dvd_powerSum
    {p N : ℕ} (hp : p.Prime) (hN : 0 < N)
    (hnot : ¬(p - 1) ∣ N) :
    (p : ℤ) ∣ ∑ j ∈ Finset.range p, (j : ℤ) ^ N := by
  letI : Fact p.Prime := ⟨hp⟩
  have hmod := sum_Ico_pow_int_modEq (p := p) N
  rw [if_neg hnot] at hmod
  have hdvdIco : (p : ℤ) ∣
      ∑ j ∈ Finset.Ico 1 p, (j : ℤ) ^ N := by
    have h := hmod.dvd
    have hneg : (p : ℤ) ∣
        -(∑ j ∈ Finset.Ico 1 p, (j : ℤ) ^ N) := by
      simpa only [zero_sub] using h
    exact dvd_neg.mp hneg
  have hsum :
      (∑ j ∈ Finset.range p, (j : ℤ) ^ N) =
        ∑ j ∈ Finset.Ico 1 p, (j : ℤ) ^ N := by
    cases p with
    | zero => simp
    | succ p =>
        rw [Finset.sum_range_eq_add_Ico (f := fun j ↦ (j : ℤ) ^ N)
          (by omega : 0 < p + 1)]
        simp [hN.ne']
  rw [hsum]
  exact hdvdIco

theorem square_dvd_shiftedPolynomialMoment
    {p N : ℕ} (hN : p ∣ N) (P : ℤ[X]) :
    (p : ℤ) ^ 2 ∣ shiftedPolynomialMoment p P N := by
  rw [shiftedPolynomialMoment, Polynomial.sum_def]
  apply Finset.dvd_sum
  intro k hk
  apply dvd_mul_of_dvd_right
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    square_dvd_shifted_pow_sub hN (k : ℤ)

theorem prime_dvd_powerSumInt
    {p N : ℕ} (hp : p.Prime) (hN : 0 < N)
    (hnot : ¬(p - 1) ∣ N) :
    (p : ℤ) ∣ powerSumInt p N := by
  simpa only [powerSumInt] using prime_dvd_powerSum hp hN hnot

/-- The result of substituting `X = exp T` into Vandiver's additive
polynomial remainder. -/
noncomputable def additiveRemainder
    (p : ℕ) (P : ℤ[X]) (b₁ : ℤ) : PowerSeries ℚ :=
  (PowerSeries.exp ℚ ^ p - 1) * polynomialExp P +
    PowerSeries.C ((p : ℤ) * b₁ : ℚ) * geomExp p

theorem polynomialExp_cyclotomic_prime
    (p : ℕ) [Fact p.Prime] :
    polynomialExp (Polynomial.cyclotomic p ℤ) = geomExp p := by
  rw [polynomialExp, Polynomial.cyclotomic_prime,
    Polynomial.eval₂_finsetSum]
  simp_rw [Polynomial.eval₂_pow, Polynomial.eval₂_X]
  rfl

theorem algebraMap_int_powerSeries_eq_C (z : ℤ) :
    algebraMap ℤ (PowerSeries ℚ) z = PowerSeries.C (z : ℚ) := by
  ext (_ | n) <;> simp

/-- Exponential substitution transports the integer-polynomial
decomposition to the additive remainder series. -/
theorem polynomialExp_eq_additiveRemainder_of_decomposition
    {p : ℕ} [Fact p.Prime] {A P : ℤ[X]} {b₁ : ℤ}
    (hA : A = (Polynomial.X ^ p - 1) * P +
      Polynomial.C ((p : ℤ) * b₁) * Polynomial.cyclotomic p ℤ) :
    polynomialExp A = additiveRemainder p P b₁ := by
  rw [hA]
  simp only [polynomialExp, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_one, Polynomial.eval₂_C]
  rw [← show polynomialExp P =
      Polynomial.eval₂ (algebraMap ℤ (PowerSeries ℚ))
        (PowerSeries.exp ℚ) P from rfl]
  rw [← show polynomialExp (Polynomial.cyclotomic p ℤ) =
      Polynomial.eval₂ (algebraMap ℤ (PowerSeries ℚ))
        (PowerSeries.exp ℚ) (Polynomial.cyclotomic p ℤ) from rfl]
  rw [polynomialExp_cyclotomic_prime, algebraMap_int_powerSeries_eq_C]
  simp [additiveRemainder]

/-- The integral value of the derivative of `additiveRemainder`. -/
def additiveRemainderDerivativeInt
    (p : ℕ) (P : ℤ[X]) (b₁ : ℤ) (N : ℕ) : ℤ :=
  shiftedPolynomialMoment p P N +
    (p : ℤ) * b₁ * powerSumInt p N

theorem formalDerivativeAtZero_additiveRemainder
    (p : ℕ) (P : ℤ[X]) (b₁ : ℤ) (N : ℕ) :
    formalDerivativeAtZero N (additiveRemainder p P b₁) =
      (additiveRemainderDerivativeInt p P b₁ N : ℚ) := by
  rw [additiveRemainder, formalDerivativeAtZero_add,
    formalDerivativeAtZero_shiftedPolynomialExp_eq_intCast,
    formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_geomExp_eq_intCast]
  simp only [additiveRemainderDerivativeInt]
  push_cast
  ring

/-- The integral derivative of Vandiver's additive remainder is divisible
by `p²` at every non-exceptional positive multiple of `p`. -/
theorem square_dvd_additiveRemainderDerivativeInt
    {p N : ℕ} (hp : p.Prime) (hN : p ∣ N) (hNpos : 0 < N)
    (hnot : ¬(p - 1) ∣ N) (P : ℤ[X]) (b₁ : ℤ) :
    (p : ℤ) ^ 2 ∣ additiveRemainderDerivativeInt p P b₁ N := by
  apply dvd_add
  · exact square_dvd_shiftedPolynomialMoment hN P
  · obtain ⟨c, hc⟩ := prime_dvd_powerSumInt hp hNpos hnot
    refine ⟨b₁ * c, ?_⟩
    rw [hc]
    ring

/-- Vandiver's high-derivative consequence: if `p ∣ N`, `N > 1`, and
`(p-1) ∤ N`, then the `N`-th derivative at zero of the substituted
additive remainder has `p`-adic valuation at least two. -/
theorem additiveRemainder_derivative_hasPadicValAtLeast_two
    {p N : ℕ} (hp : p.Prime) (hN : p ∣ N) (hNgt : 1 < N)
    (hnot : ¬(p - 1) ∣ N) (P : ℤ[X]) (b₁ : ℤ) :
    HasPadicValAtLeast p 2
      (formalDerivativeAtZero N (additiveRemainder p P b₁)) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ :=
    square_dvd_additiveRemainderDerivativeInt hp hN
      (by omega) hnot P b₁
  rw [formalDerivativeAtZero_additiveRemainder, hc]
  have hp2 := HasPadicValAtLeast.primePow (p := p) 2
  have hc0 := HasPadicValAtLeast.intCast (p := p) c
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] using
    hp2.mul hc0

/-- The polynomial hypotheses from Vandiver's preceding step produce an
additive remainder representation after exponential substitution. -/
theorem exists_polynomialExp_eq_additiveRemainder
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (A : ℤ[X]) (hA : aeval ζ A = 0)
    (hsquare : (p : ℤ) ^ 2 ∣ A.eval 1) :
    ∃ (P : ℤ[X]) (b₁ : ℤ),
      polynomialExp A = additiveRemainder p P b₁ := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, b, hdecomp, heval, hb⟩ :=
    Fermat.Irregular.VandiverPolynomialRemainder.exists_polynomial_remainder_decomposition_of_square_dvd_eval
      hp hζ A hA hsquare
  obtain ⟨b₁, rfl⟩ := hb
  exact ⟨P, b₁,
    polynomialExp_eq_additiveRemainder_of_decomposition hdecomp⟩

/-- Combined bridge from primitive-root vanishing and `p² ∣ A(1)` to
Vandiver's high-derivative valuation bound. -/
theorem polynomialExp_derivative_hasPadicValAtLeast_two
    {K : Type*} [Field K] [CharZero K]
    {p N : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (A : ℤ[X]) (hA : aeval ζ A = 0)
    (hsquare : (p : ℤ) ^ 2 ∣ A.eval 1)
    (hN : p ∣ N) (hNgt : 1 < N) (hnot : ¬(p - 1) ∣ N) :
    HasPadicValAtLeast p 2
      (formalDerivativeAtZero N (polynomialExp A)) := by
  obtain ⟨P, b₁, hseries⟩ :=
    exists_polynomialExp_eq_additiveRemainder hp hζ A hA hsquare
  rw [hseries]
  exact additiveRemainder_derivative_hasPadicValAtLeast_two
    hp hN hNgt hnot P b₁

end Fermat.Irregular.VandiverRemainderDerivative
