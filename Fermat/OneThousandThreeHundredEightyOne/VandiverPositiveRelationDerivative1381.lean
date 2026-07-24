import Fermat.Irregular.VandiverLogDerivativeValuation
import Fermat.OneThousandThreeHundredEightyOne.VandiverDeepPolynomial
import Fermat.OneThousandThreeHundredEightyOne.VandiverNormalizedRelationDerivative1381

/-!
# Vandiver's positive-relation derivative congruence at 1381

This file completes the polynomial-remainder calculation for a relation
with natural exponents in the 689 actual diagonal units at exponent `1381`.

A deep relation first gives the integer polynomial

`A = P - C - 1381² H`

from `VandiverDeepPolynomial`, with `A(zeta) = 0` and `1381² ∣ A(1)`.
After substituting `W = exp V`, the generic remainder theorem and the
inverse-series recursion show that the selected logarithmic derivatives
have `1381`-adic valuation at least two.

Finally, `VandiverPolynomialUnits` identifies this logarithmic derivative
with `relationDerivative1381`. The endpoint is the exact
`PositiveRelationDerivativeCongruences1381` premise consumed by
`VandiverLemmaTwoAssembly`.
-/

open scoped BigOperators NumberField

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverPositiveRelationDerivative

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverRemainderDerivative
open Fermat.Irregular.VandiverLogDerivativeValuation
open Fermat.Irregular.Voronoi
open Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalUnits
open Fermat.OneThousandThreeHundredEightyOne.VandiverDerivativeValuation
open Fermat.OneThousandThreeHundredEightyOne.VandiverDiagonalDerivative
open Fermat.OneThousandThreeHundredEightyOne.VandiverPolynomialUnits
open Fermat.OneThousandThreeHundredEightyOne.VandiverDeepPolynomial
open Fermat.OneThousandThreeHundredEightyOne.VandiverNormalizedRelationDerivative

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1381} ℚ K]

/-! ## The positive vanishing polynomial -/

/-- Specialization of the deep polynomial construction to natural
exponents. The negative relation polynomial becomes `1`, leaving the
source's positive polynomial in the exact form `P - C - 1381² H`. -/
theorem exists_vanishingPositiveRelationPolynomial1381
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1381)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (b : SourceIndex 1381 → ℕ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 2762 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 1381)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit1381 hzeta i ^ b i) :
    ∃ H : Polynomial ℤ,
      let P := positiveRelationPolynomial1381 b
      let C : ℤ := c ^ (1381 * (1380 * t))
      let A := vanishingRelationPolynomial1381 P 1 H C
      Polynomial.aeval zeta A = 0 ∧
        (1381 : ℤ) ^ 2 ∣ A.eval 1 := by
  have hrelZ : u ^ t =
      ∏ i, diagonalVandiverUnit1381 hzeta i ^ (b i : ℤ) := by
    simpa only [zpow_natCast] using hrel
  obtain ⟨H, hzero, hsquare⟩ :=
    exists_vanishingRelationPolynomial1381 hzeta u c t
      (fun i ↦ (b i : ℤ)) hdeep hrelZ
  refine ⟨H, ?_, ?_⟩
  · simpa [positiveRelationPolynomial1381] using hzero
  · simpa [positiveRelationPolynomial1381] using hsquare

/-- Exponential substitution turns `A = P - C - 1381² H` into the additive
source decomposition used in the derivative recursion. -/
theorem polynomialExp_vanishingRelationPolynomial1381
    (P H : Polynomial ℤ) (C : ℤ) :
    polynomialExp P =
      PowerSeries.C (C : ℚ) +
        PowerSeries.C ((1381 : ℤ) ^ 2 : ℚ) * polynomialExp H +
        polynomialExp (vanishingRelationPolynomial1381 P 1 H C) := by
  rw [vanishingRelationPolynomial1381]
  simp only [polynomialExp, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_one]
  rw [algebraMap_int_powerSeries_eq_C,
    algebraMap_int_powerSeries_eq_C]
  ring_nf

/-! ## Integral derivatives and the source constant -/

/-- The constant coefficient after exponential substitution is evaluation
of the original integer polynomial at `1`. -/
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

/-- The integral power moment which is the derivative of `P(exp V)` at
zero. -/
def polynomialMomentInt (P : Polynomial ℤ) (N : ℕ) : ℤ :=
  P.sum fun k a ↦ a * (k : ℤ) ^ N

theorem formalDerivativeAtZero_polynomialExp_eq_intCast
    (P : Polynomial ℤ) (N : ℕ) :
    formalDerivativeAtZero N (polynomialExp P) =
      (polynomialMomentInt P N : ℚ) := by
  rw [formalDerivativeAtZero_polynomialExp]
  simp only [polynomialMomentInt, Polynomial.sum_def]
  push_cast
  rfl

/-- Every derivative of `1381² * H(exp V)` has `1381`-adic valuation at
least two. -/
theorem scaledPolynomialExp1381sq_derivative_hasPadicValAtLeast_two
    (P : Polynomial ℤ) (N : ℕ) :
    HasPadicValAtLeast 1381 2
      (formalDerivativeAtZero N
        (PowerSeries.C ((1381 : ℤ) ^ 2 : ℚ) * polynomialExp P)) := by
  rw [formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_polynomialExp_eq_intCast]
  have hp2 := HasPadicValAtLeast.primePow (p := 1381) 2
  have hmoment :=
    HasPadicValAtLeast.intCast (p := 1381) (polynomialMomentInt P N)
  convert hp2.mul hmoment using 1

/-- Since `P(1) ≡ 1 mod 1381²`, the positive relation polynomial is not
divisible by `1381` at `1`. -/
theorem oneThousandThreeHundredEightyOne_not_dvd_eval_one_positiveRelationPolynomial1381
    (b : SourceIndex 1381 → ℕ) :
    ¬(1381 : ℤ) ∣
      (positiveRelationPolynomial1381 b).eval 1 := by
  have hmod :=
    eval_one_positiveRelationPolynomial1381_mod_sq b
  have hzero :
      ((((positiveRelationPolynomial1381 b).eval 1 - 1 : ℤ)) :
        ZMod (1381 ^ 2)) = 0 := by
    push_cast
    rw [hmod]
    ring
  have hsquare :
      (((1381 ^ 2 : ℕ) : ℤ) ∣
        (positiveRelationPolynomial1381 b).eval 1 - 1) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hOneThousandThreeHundredEightyOne :
      (1381 : ℤ) ∣
        (positiveRelationPolynomial1381 b).eval 1 - 1 :=
    (by norm_num : (1381 : ℤ) ∣ ((1381 ^ 2 : ℕ) : ℤ)).trans hsquare
  intro heval
  have hone : (1381 : ℤ) ∣ 1 := by
    convert dvd_sub heval hOneThousandThreeHundredEightyOne using 1
    ring
  norm_num at hone

theorem constantCoeff_positiveRelationPolynomial1381_ne_zero
    (b : SourceIndex 1381 → ℕ) :
    PowerSeries.constantCoeff
      (polynomialExp (positiveRelationPolynomial1381 b)) ≠ 0 := by
  rw [constantCoeff_polynomialExp]
  exact_mod_cast
    (show (positiveRelationPolynomial1381 b).eval 1 ≠ 0 from
      fun hzero ↦
        oneThousandThreeHundredEightyOne_not_dvd_eval_one_positiveRelationPolynomial1381 b
          (hzero ▸ dvd_zero 1381))

theorem constantCoeff_positiveRelationPolynomial1381_padicVal_eq_zero
    (b : SourceIndex 1381 → ℕ) :
    padicValRat 1381
      (PowerSeries.constantCoeff
        (polynomialExp (positiveRelationPolynomial1381 b))) = 0 := by
  rw [constantCoeff_polynomialExp, padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd
      (oneThousandThreeHundredEightyOne_not_dvd_eval_one_positiveRelationPolynomial1381 b)]
  norm_num

/-! ## The specialized logarithmic derivative -/

omit [IsCyclotomicExtension {1381} ℚ K] in
/-- The polynomial-remainder and inverse-series recursion specialized to
one positive relation polynomial.

At the selected row `k`, the top derivative order is
`N = (2 * sourceNumber k) * 1381`. Thus `1381 ∣ N`, while the certified
source range gives `1380 ∤ N`, exactly the hypotheses of the generic
remainder theorem. -/
theorem positiveRelation_logarithmicDerivative_hasPadicValAtLeast_two
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1381)
    (b : SourceIndex 1381 → ℕ) (H : Polynomial ℤ) (C : ℤ)
    (hzero : Polynomial.aeval zeta
      (vanishingRelationPolynomial1381
        (positiveRelationPolynomial1381 b) 1 H C) = 0)
    (hsquare : (1381 : ℤ) ^ 2 ∣
      (vanishingRelationPolynomial1381
        (positiveRelationPolynomial1381 b) 1 H C).eval 1) :
    ∀ k : SourceIndex 1381,
      HasPadicValAtLeast 1381 2
        (formalDerivativeAtZero (sourceDerivativeOrder1381 k)
          (logarithmicDerivative
            (polynomialExp (positiveRelationPolynomial1381 b)))) := by
  let P := positiveRelationPolynomial1381 b
  let A := vanishingRelationPolynomial1381 P 1 H C
  have hzeroA : Polynomial.aeval zeta A = 0 := by
    simpa only [A, P] using hzero
  have hsquareA : (1381 : ℤ) ^ 2 ∣ A.eval 1 := by
    simpa only [A, P] using hsquare
  obtain ⟨V, b₁, hAseries⟩ :=
    exists_polynomialExp_eq_additiveRemainder
      (p := 1381) (by norm_num) hzeta A hzeroA hsquareA
  have hsource :
      polynomialExp P =
        PowerSeries.C (C : ℚ) +
          PowerSeries.C ((1381 : ℤ) ^ 2 : ℚ) * polynomialExp H +
          additiveRemainder 1381 V b₁ := by
    calc
      polynomialExp P =
          PowerSeries.C (C : ℚ) +
            PowerSeries.C ((1381 : ℤ) ^ 2 : ℚ) * polynomialExp H +
            polynomialExp A := by
              simpa only [A] using
                polynomialExp_vanishingRelationPolynomial1381 P H C
      _ = _ := by rw [hAseries]
  intro k
  let N := derivativeBernoulliIndex1381 k
  have hNpos : 0 < N := by
    simp [N, derivativeBernoulliIndex1381, sourceNumber]
  have hNgt : 1 < N := by
    simp only [N, derivativeBernoulliIndex1381, sourceNumber]
    omega
  have hNdiv : 1381 ∣ N := by
    refine ⟨2 * sourceNumber k, ?_⟩
    simp only [N, derivativeBernoulliIndex1381]
    ring
  have hNnot : ¬(1381 - 1) ∣ N := by
    simpa only [show 1381 - 1 = 1380 by norm_num, N] using
      oneThousandThreeHundredEighty_not_dvd_derivativeBernoulliIndex1381 k
  have hlog :
      HasPadicValAtLeast 1381 2
        (formalDerivativeAtZero (N - 1)
          (logarithmicDerivative (polynomialExp P))) := by
    apply logarithmicDerivative_formalDerivative_hasPadicValAtLeast_two
      (p := 1381) (N := N) (by norm_num) hNpos
        (polynomialExp P)
    · simpa only [P] using
        constantCoeff_positiveRelationPolynomial1381_ne_zero b
    · simpa only [P] using
        constantCoeff_positiveRelationPolynomial1381_padicVal_eq_zero b
    · intro s hs hsN
      rw [hsource, formalDerivativeAtZero_add,
        formalDerivativeAtZero_add]
      have hconstant :
          formalDerivativeAtZero s (PowerSeries.C (C : ℚ)) = 0 := by
        rw [formalDerivativeAtZero,
          PowerSeries.coeff_C_of_ne_zero hs.ne']
        ring
      rw [hconstant, zero_add]
      have hscaled :=
        scaledPolynomialExp1381sq_derivative_hasPadicValAtLeast_two H s
      have hremainder :=
        additiveRemainder_derivative_hasPadicValAtLeast_one
          (p := 1381) (by norm_num) s V b₁
      exact (hscaled.mono (by omega)).add hremainder
    · rw [hsource, formalDerivativeAtZero_add,
        formalDerivativeAtZero_add]
      have hconstant :
          formalDerivativeAtZero N (PowerSeries.C (C : ℚ)) = 0 := by
        rw [formalDerivativeAtZero,
          PowerSeries.coeff_C_of_ne_zero hNpos.ne']
        ring
      rw [hconstant, zero_add]
      exact
        (scaledPolynomialExp1381sq_derivative_hasPadicValAtLeast_two H N).add
          (additiveRemainder_derivative_hasPadicValAtLeast_two
            (by norm_num) hNdiv hNgt hNnot V b₁)
  simpa only [N, sourceDerivativeOrder1381] using hlog

/-- The derivative of the logarithm of the positive relation polynomial is
exactly the existing exponent-weighted `relationDerivative1381`. -/
theorem relationDerivative1381_natCast_eq
    (b : SourceIndex 1381 → ℕ) (k : SourceIndex 1381) :
    relationDerivative1381 (fun i ↦ (b i : ℤ)) k =
      formalDerivativeAtZero (sourceDerivativeOrder1381 k)
        (logarithmicDerivative
          (polynomialExp (positiveRelationPolynomial1381 b))) := by
  rw [show polynomialExp (positiveRelationPolynomial1381 b) =
      polynomialExp1381 (positiveRelationPolynomial1381 b) by rfl]
  rw [formalDerivativeAtZero_positiveRelationPolynomial1381]
  rw [relationDerivative1381]
  apply Finset.sum_congr rfl
  intro i hi
  norm_cast

/-! ## Exact assembly premise -/

/-- Every deep positive relation in the 689 actual diagonal units has all
of Vandiver's selected relation derivatives divisible by `1381²`. -/
theorem positiveRelationDerivativeCongruences1381
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1381) :
    PositiveRelationDerivativeCongruences1381 hzeta := by
  intro v t b hvdeep hrel k
  obtain ⟨c, hdeep⟩ := hvdeep
  obtain ⟨H, hzero, hsquare⟩ :=
    exists_vanishingPositiveRelationPolynomial1381
      hzeta v c t b hdeep hrel
  rw [relationDerivative1381_natCast_eq]
  exact
    positiveRelation_logarithmicDerivative_hasPadicValAtLeast_two
      hzeta b H (c ^ (1381 * (1380 * t))) hzero hsquare k

end

end Fermat.OneThousandThreeHundredEightyOne.VandiverPositiveRelationDerivative
