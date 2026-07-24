import Fermat.Irregular.VandiverLogDerivativeValuation
import Fermat.FourHundredNinetyOne.VandiverDeepPolynomial
import Fermat.FourHundredNinetyOne.VandiverNormalizedRelationDerivative

/-!
# Vandiver's positive-relation derivative congruence at 491

This file completes the polynomial-remainder calculation for a relation
with natural exponents in the 244 actual diagonal units at exponent `491`.

A deep relation first gives the integer polynomial

`A = P - C - 491² H`

from `VandiverDeepPolynomial`, with `A(zeta) = 0` and `491² ∣ A(1)`.
After substituting `W = exp V`, the generic remainder theorem and the
inverse-series recursion show that the selected logarithmic derivatives
have `491`-adic valuation at least two.

Finally, `VandiverPolynomialUnits` identifies this logarithmic derivative
with `relationDerivative491`.  The endpoint is the exact
`PositiveRelationDerivativeCongruences491` premise consumed by
`VandiverLemmaTwoAssembly`.
-/

open scoped BigOperators NumberField

namespace Fermat.FourHundredNinetyOne.VandiverPositiveRelationDerivative

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverRemainderDerivative
open Fermat.Irregular.VandiverLogDerivativeValuation
open Fermat.Irregular.Voronoi
open Fermat.FourHundredNinetyOne.VandiverDiagonalUnits
open Fermat.FourHundredNinetyOne.VandiverDerivativeValuation
open Fermat.FourHundredNinetyOne.VandiverDiagonalDerivative
open Fermat.FourHundredNinetyOne.VandiverPolynomialUnits
open Fermat.FourHundredNinetyOne.VandiverDeepPolynomial
open Fermat.FourHundredNinetyOne.VandiverNormalizedRelationDerivative

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {491} ℚ K]

/-! ## The positive vanishing polynomial -/

/-- Specialization of the deep polynomial construction to natural
exponents.  The negative relation polynomial becomes `1`, leaving the
source's positive polynomial in the exact form `P - C - 491² H`. -/
theorem exists_vanishingPositiveRelationPolynomial491
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (b : SourceIndex 491 → ℕ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 982 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 491)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit491 hzeta i ^ b i) :
    ∃ H : Polynomial ℤ,
      let P := positiveRelationPolynomial491 b
      let C : ℤ := c ^ (491 * (490 * t))
      let A := vanishingRelationPolynomial491 P 1 H C
      Polynomial.aeval zeta A = 0 ∧
        (491 : ℤ) ^ 2 ∣ A.eval 1 := by
  have hrelZ : u ^ t =
      ∏ i, diagonalVandiverUnit491 hzeta i ^ (b i : ℤ) := by
    simpa only [zpow_natCast] using hrel
  obtain ⟨H, hzero, hsquare⟩ :=
    exists_vanishingRelationPolynomial491 hzeta u c t
      (fun i ↦ (b i : ℤ)) hdeep hrelZ
  refine ⟨H, ?_, ?_⟩
  · simpa [positiveRelationPolynomial491] using hzero
  · simpa [positiveRelationPolynomial491] using hsquare

/-- Exponential substitution turns `A = P - C - 491² H` into the additive
source decomposition used in the derivative recursion. -/
theorem polynomialExp_vanishingRelationPolynomial491
    (P H : Polynomial ℤ) (C : ℤ) :
    polynomialExp P =
      PowerSeries.C (C : ℚ) +
        PowerSeries.C ((491 : ℤ) ^ 2 : ℚ) * polynomialExp H +
        polynomialExp (vanishingRelationPolynomial491 P 1 H C) := by
  rw [vanishingRelationPolynomial491]
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

/-- Every derivative of `491² * H(exp V)` has `491`-adic valuation at
least two. -/
theorem scaledPolynomialExp491sq_derivative_hasPadicValAtLeast_two
    (P : Polynomial ℤ) (N : ℕ) :
    HasPadicValAtLeast 491 2
      (formalDerivativeAtZero N
        (PowerSeries.C ((491 : ℤ) ^ 2 : ℚ) * polynomialExp P)) := by
  rw [formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_polynomialExp_eq_intCast]
  have hp2 := HasPadicValAtLeast.primePow (p := 491) 2
  have hmoment :=
    HasPadicValAtLeast.intCast (p := 491) (polynomialMomentInt P N)
  convert hp2.mul hmoment using 1

/-- Since `P(1) ≡ 1 mod 491²`, the positive relation polynomial is not
divisible by `491` at `1`. -/
theorem fourHundredNinetyOne_not_dvd_eval_one_positiveRelationPolynomial491
    (b : SourceIndex 491 → ℕ) :
    ¬(491 : ℤ) ∣
      (positiveRelationPolynomial491 b).eval 1 := by
  have hmod :=
    eval_one_positiveRelationPolynomial491_mod_sq b
  have hzero :
      ((((positiveRelationPolynomial491 b).eval 1 - 1 : ℤ)) :
        ZMod (491 ^ 2)) = 0 := by
    push_cast
    rw [hmod]
    ring
  have hsquare :
      (((491 ^ 2 : ℕ) : ℤ) ∣
        (positiveRelationPolynomial491 b).eval 1 - 1) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hFourHundredNinetyOne :
      (491 : ℤ) ∣
        (positiveRelationPolynomial491 b).eval 1 - 1 :=
    (by norm_num : (491 : ℤ) ∣ ((491 ^ 2 : ℕ) : ℤ)).trans hsquare
  intro heval
  have hone : (491 : ℤ) ∣ 1 := by
    convert dvd_sub heval hFourHundredNinetyOne using 1
    ring
  norm_num at hone

theorem constantCoeff_positiveRelationPolynomial491_ne_zero
    (b : SourceIndex 491 → ℕ) :
    PowerSeries.constantCoeff
      (polynomialExp (positiveRelationPolynomial491 b)) ≠ 0 := by
  rw [constantCoeff_polynomialExp]
  exact_mod_cast
    (show (positiveRelationPolynomial491 b).eval 1 ≠ 0 from
      fun hzero ↦
        fourHundredNinetyOne_not_dvd_eval_one_positiveRelationPolynomial491 b
          (hzero ▸ dvd_zero 491))

theorem constantCoeff_positiveRelationPolynomial491_padicVal_eq_zero
    (b : SourceIndex 491 → ℕ) :
    padicValRat 491
      (PowerSeries.constantCoeff
        (polynomialExp (positiveRelationPolynomial491 b))) = 0 := by
  rw [constantCoeff_polynomialExp, padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd
      (fourHundredNinetyOne_not_dvd_eval_one_positiveRelationPolynomial491 b)]
  norm_num

/-! ## The specialized logarithmic derivative -/

omit [IsCyclotomicExtension {491} ℚ K] in
/-- The polynomial-remainder and inverse-series recursion specialized to
one positive relation polynomial.

At the selected row `k`, the top derivative order is
`N = (2 * sourceNumber k) * 491`.  Thus `491 ∣ N`, while the certified
source range gives `490 ∤ N`, exactly the hypotheses of the generic
remainder theorem. -/
theorem positiveRelation_logarithmicDerivative_hasPadicValAtLeast_two
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491)
    (b : SourceIndex 491 → ℕ) (H : Polynomial ℤ) (C : ℤ)
    (hzero : Polynomial.aeval zeta
      (vanishingRelationPolynomial491
        (positiveRelationPolynomial491 b) 1 H C) = 0)
    (hsquare : (491 : ℤ) ^ 2 ∣
      (vanishingRelationPolynomial491
        (positiveRelationPolynomial491 b) 1 H C).eval 1) :
    ∀ k : SourceIndex 491,
      HasPadicValAtLeast 491 2
        (formalDerivativeAtZero (sourceDerivativeOrder491 k)
          (logarithmicDerivative
            (polynomialExp (positiveRelationPolynomial491 b)))) := by
  let P := positiveRelationPolynomial491 b
  let A := vanishingRelationPolynomial491 P 1 H C
  have hzeroA : Polynomial.aeval zeta A = 0 := by
    simpa only [A, P] using hzero
  have hsquareA : (491 : ℤ) ^ 2 ∣ A.eval 1 := by
    simpa only [A, P] using hsquare
  obtain ⟨V, b₁, hAseries⟩ :=
    exists_polynomialExp_eq_additiveRemainder
      (p := 491) (by norm_num) hzeta A hzeroA hsquareA
  have hsource :
      polynomialExp P =
        PowerSeries.C (C : ℚ) +
          PowerSeries.C ((491 : ℤ) ^ 2 : ℚ) * polynomialExp H +
          additiveRemainder 491 V b₁ := by
    calc
      polynomialExp P =
          PowerSeries.C (C : ℚ) +
            PowerSeries.C ((491 : ℤ) ^ 2 : ℚ) * polynomialExp H +
            polynomialExp A := by
              simpa only [A] using
                polynomialExp_vanishingRelationPolynomial491 P H C
      _ = _ := by rw [hAseries]
  intro k
  let N := derivativeBernoulliIndex491 k
  have hNpos : 0 < N := by
    simp [N, derivativeBernoulliIndex491, sourceNumber]
  have hNgt : 1 < N := by
    simp only [N, derivativeBernoulliIndex491, sourceNumber]
    omega
  have hNdiv : 491 ∣ N := by
    refine ⟨2 * sourceNumber k, ?_⟩
    simp only [N, derivativeBernoulliIndex491]
    ring
  have hNnot : ¬(491 - 1) ∣ N := by
    simpa only [show 491 - 1 = 490 by norm_num, N] using
      fourHundredNinety_not_dvd_derivativeBernoulliIndex491 k
  have hlog :
      HasPadicValAtLeast 491 2
        (formalDerivativeAtZero (N - 1)
          (logarithmicDerivative (polynomialExp P))) := by
    apply logarithmicDerivative_formalDerivative_hasPadicValAtLeast_two
      (p := 491) (N := N) (by norm_num) hNpos
        (polynomialExp P)
    · simpa only [P] using
        constantCoeff_positiveRelationPolynomial491_ne_zero b
    · simpa only [P] using
        constantCoeff_positiveRelationPolynomial491_padicVal_eq_zero b
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
        scaledPolynomialExp491sq_derivative_hasPadicValAtLeast_two H s
      have hremainder :=
        additiveRemainder_derivative_hasPadicValAtLeast_one
          (p := 491) (by norm_num) s V b₁
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
        (scaledPolynomialExp491sq_derivative_hasPadicValAtLeast_two H N).add
          (additiveRemainder_derivative_hasPadicValAtLeast_two
            (by norm_num) hNdiv hNgt hNnot V b₁)
  simpa only [N, sourceDerivativeOrder491] using hlog

/-- The derivative of the logarithm of the positive relation polynomial is
exactly the existing exponent-weighted `relationDerivative491`. -/
theorem relationDerivative491_natCast_eq
    (b : SourceIndex 491 → ℕ) (k : SourceIndex 491) :
    relationDerivative491 (fun i ↦ (b i : ℤ)) k =
      formalDerivativeAtZero (sourceDerivativeOrder491 k)
        (logarithmicDerivative
          (polynomialExp (positiveRelationPolynomial491 b))) := by
  rw [show polynomialExp (positiveRelationPolynomial491 b) =
      polynomialExp491 (positiveRelationPolynomial491 b) by rfl]
  rw [formalDerivativeAtZero_positiveRelationPolynomial491]
  rw [relationDerivative491]
  apply Finset.sum_congr rfl
  intro i hi
  norm_cast

/-! ## Exact assembly premise -/

/-- Every deep positive relation in the 244 actual diagonal units has all
of Vandiver's selected relation derivatives divisible by `491²`. -/
theorem positiveRelationDerivativeCongruences491
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) :
    PositiveRelationDerivativeCongruences491 hzeta := by
  intro v t b hvdeep hrel k
  obtain ⟨c, hdeep⟩ := hvdeep
  obtain ⟨H, hzero, hsquare⟩ :=
    exists_vanishingPositiveRelationPolynomial491
      hzeta v c t b hdeep hrel
  rw [relationDerivative491_natCast_eq]
  exact
    positiveRelation_logarithmicDerivative_hasPadicValAtLeast_two
      hzeta b H (c ^ (491 * (490 * t))) hzero hsquare k

end

end Fermat.FourHundredNinetyOne.VandiverPositiveRelationDerivative
