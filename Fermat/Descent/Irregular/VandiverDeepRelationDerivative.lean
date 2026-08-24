import Fermat.Descent.Irregular.VandiverLogDerivativeValuation

/-!
# Prime-generic deep-polynomial logarithmic derivatives

This is the prime-uniform part of Vandiver's positive-relation derivative
calculation. A deep unit relation has already supplied an integer polynomial
`A` which vanishes at a primitive `p`th root and whose value at one is
divisible by `p²`. If the positive source polynomial differs from `A` by a
constant and a `p²`-scaled integral polynomial, its selected logarithmic
derivative has `p`-adic valuation at least two.
-/

namespace Fermat.Irregular.VandiverDeepRelationDerivative

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverRemainderDerivative
open Fermat.Irregular.VandiverLogDerivativeValuation
open Fermat.Irregular.Voronoi

/-- The integral power moment obtained by differentiating `P(exp V)` at
zero. -/
def polynomialMomentInt (P : Polynomial ℤ) (N : ℕ) : ℤ :=
  P.sum fun k a ↦ a * (k : ℤ) ^ N

/-- The constant coefficient of `P(exp V)` is `P(1)`. -/
theorem constantCoeff_polynomialExp (P : Polynomial ℤ) :
    PowerSeries.constantCoeff (polynomialExp P) =
      ((Polynomial.eval (1 : ℤ) P : ℤ) : ℚ) := by
  rw [polynomialExp_eq_sum, Polynomial.eval_eq_sum,
    Polynomial.sum_def]
  push_cast
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp

/-- Every formal derivative of `P(exp V)` is its integral power moment. -/
theorem formalDerivativeAtZero_polynomialExp_eq_intCast
    (P : Polynomial ℤ) (N : ℕ) :
    formalDerivativeAtZero N (polynomialExp P) =
      (polynomialMomentInt P N : ℚ) := by
  rw [formalDerivativeAtZero_polynomialExp]
  simp only [polynomialMomentInt, Polynomial.sum_def]
  push_cast
  rfl

/-- Every derivative of `p² * H(exp V)` has `p`-adic valuation at least
two. -/
theorem scaledPolynomialExp_sq_derivative_hasPadicValAtLeast_two
    {p : ℕ} (hp : p.Prime) (P : Polynomial ℤ) (N : ℕ) :
    HasPadicValAtLeast p 2
      (formalDerivativeAtZero N
        (PowerSeries.C ((p : ℤ) ^ 2 : ℚ) * polynomialExp P)) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_polynomialExp_eq_intCast]
  have hp2 := HasPadicValAtLeast.primePow (p := p) 2
  have hmoment :=
    HasPadicValAtLeast.intCast (p := p) (polynomialMomentInt P N)
  convert hp2.mul hmoment using 1

/-- A deep polynomial relation gives the selected logarithmic derivative
valuation uniformly in the prime.

The source equality is the exact additive decomposition used in the
fixed-prime developments: a constant, a `p²`-scaled integral series, and a
polynomial which vanishes at the chosen primitive root. -/
theorem logarithmicDerivative_of_deepPolynomial
    {K : Type*} [Field K] [CharZero K]
    {p N : ℕ} (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (P H A : Polynomial ℤ) (C : ℤ)
    (hsource :
      polynomialExp P =
        PowerSeries.C (C : ℚ) +
          PowerSeries.C ((p : ℤ) ^ 2 : ℚ) * polynomialExp H +
          polynomialExp A)
    (hzero : Polynomial.aeval ζ A = 0)
    (hsquare : (p : ℤ) ^ 2 ∣ A.eval 1)
    (hPunit : ¬(p : ℤ) ∣ P.eval 1)
    (hNpos : 0 < N) (hNdiv : p ∣ N) (hNgt : 1 < N)
    (hNnot : ¬(p - 1) ∣ N) :
    HasPadicValAtLeast p 2
      (formalDerivativeAtZero (N - 1)
        (logarithmicDerivative (polynomialExp P))) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨V, b₁, hAseries⟩ :=
    exists_polynomialExp_eq_additiveRemainder
      hp hζ A hzero hsquare
  have hsource' :
      polynomialExp P =
        PowerSeries.C (C : ℚ) +
          PowerSeries.C ((p : ℤ) ^ 2 : ℚ) * polynomialExp H +
          additiveRemainder p V b₁ := by
    calc
      polynomialExp P =
          PowerSeries.C (C : ℚ) +
            PowerSeries.C ((p : ℤ) ^ 2 : ℚ) * polynomialExp H +
            polynomialExp A := hsource
      _ = _ := by rw [hAseries]
  apply logarithmicDerivative_formalDerivative_hasPadicValAtLeast_two
    hp hNpos (polynomialExp P)
  · rw [constantCoeff_polynomialExp]
    exact_mod_cast
      (show P.eval 1 ≠ 0 from
        fun hzeroEval ↦ hPunit (hzeroEval ▸ dvd_zero (p : ℤ)))
  · rw [constantCoeff_polynomialExp, padicValRat.of_int,
      padicValInt.eq_zero_of_not_dvd hPunit]
    norm_num
  · intro s hs hsN
    rw [hsource', formalDerivativeAtZero_add,
      formalDerivativeAtZero_add]
    have hconstant :
        formalDerivativeAtZero s (PowerSeries.C (C : ℚ)) = 0 := by
      rw [formalDerivativeAtZero,
        PowerSeries.coeff_C_of_ne_zero hs.ne']
      ring
    rw [hconstant, zero_add]
    have hscaled :=
      scaledPolynomialExp_sq_derivative_hasPadicValAtLeast_two hp H s
    have hremainder :=
      additiveRemainder_derivative_hasPadicValAtLeast_one hp s V b₁
    exact (hscaled.mono (by omega)).add hremainder
  · rw [hsource', formalDerivativeAtZero_add,
      formalDerivativeAtZero_add]
    have hconstant :
        formalDerivativeAtZero N (PowerSeries.C (C : ℚ)) = 0 := by
      rw [formalDerivativeAtZero,
        PowerSeries.coeff_C_of_ne_zero hNpos.ne']
      ring
    rw [hconstant, zero_add]
    exact
      (scaledPolynomialExp_sq_derivative_hasPadicValAtLeast_two hp H N).add
        (additiveRemainder_derivative_hasPadicValAtLeast_two
          hp hNdiv hNgt hNnot V b₁)

end

end Fermat.Irregular.VandiverDeepRelationDerivative
