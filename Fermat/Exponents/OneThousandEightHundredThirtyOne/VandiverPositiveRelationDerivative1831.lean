import Fermat.Descent.Irregular.VandiverLogDerivativeValuation
import Fermat.Exponents.OneThousandEightHundredThirtyOne.VandiverDeepPolynomial
import Fermat.Exponents.OneThousandEightHundredThirtyOne.VandiverNormalizedRelationDerivative1831

/-!
# Vandiver's positive-relation derivative congruence at 1831

This file completes the polynomial-remainder calculation for a relation
with natural exponents in the 914 actual diagonal units at exponent `1831`.

A deep relation first gives the integer polynomial

`A = P - C - 1831² H`

from `VandiverDeepPolynomial`, with `A(zeta) = 0` and `1831² ∣ A(1)`.
After substituting `W = exp V`, the generic remainder theorem and the
inverse-series recursion show that the selected logarithmic derivatives
have `1831`-adic valuation at least two.

Finally, `VandiverPolynomialUnits` identifies this logarithmic derivative
with `relationDerivative1831`. The endpoint is the exact
`PositiveRelationDerivativeCongruences1831` premise consumed by
`VandiverLemmaTwoAssembly`.
-/

open scoped BigOperators NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.VandiverPositiveRelationDerivative

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverRemainderDerivative
open Fermat.Irregular.VandiverLogDerivativeValuation
open Fermat.Irregular.Voronoi
open Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalUnits
open Fermat.OneThousandEightHundredThirtyOne.VandiverDerivativeValuation
open Fermat.OneThousandEightHundredThirtyOne.VandiverDiagonalDerivative
open Fermat.OneThousandEightHundredThirtyOne.VandiverPolynomialUnits
open Fermat.OneThousandEightHundredThirtyOne.VandiverDeepPolynomial
open Fermat.OneThousandEightHundredThirtyOne.VandiverNormalizedRelationDerivative

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

/-! ## The positive vanishing polynomial -/

/-- Specialization of the deep polynomial construction to natural
exponents. The negative relation polynomial becomes `1`, leaving the
source's positive polynomial in the exact form `P - C - 1831² H`. -/
theorem exists_vanishingPositiveRelationPolynomial1831
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1831)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (b : SourceIndex 1831 → ℕ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 3662 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 1831)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit1831 hzeta i ^ b i) :
    ∃ H : Polynomial ℤ,
      let P := positiveRelationPolynomial1831 b
      let C : ℤ := c ^ (1831 * (1830 * t))
      let A := vanishingRelationPolynomial1831 P 1 H C
      Polynomial.aeval zeta A = 0 ∧
        (1831 : ℤ) ^ 2 ∣ A.eval 1 := by
  have hrelZ : u ^ t =
      ∏ i, diagonalVandiverUnit1831 hzeta i ^ (b i : ℤ) := by
    simpa only [zpow_natCast] using hrel
  obtain ⟨H, hzero, hsquare⟩ :=
    exists_vanishingRelationPolynomial1831 hzeta u c t
      (fun i ↦ (b i : ℤ)) hdeep hrelZ
  refine ⟨H, ?_, ?_⟩
  · simpa [positiveRelationPolynomial1831] using hzero
  · simpa [positiveRelationPolynomial1831] using hsquare

/-- Exponential substitution turns `A = P - C - 1831² H` into the additive
source decomposition used in the derivative recursion. -/
theorem polynomialExp_vanishingRelationPolynomial1831
    (P H : Polynomial ℤ) (C : ℤ) :
    polynomialExp P =
      PowerSeries.C (C : ℚ) +
        PowerSeries.C ((1831 : ℤ) ^ 2 : ℚ) * polynomialExp H +
        polynomialExp (vanishingRelationPolynomial1831 P 1 H C) := by
  rw [vanishingRelationPolynomial1831]
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

/-- Every derivative of `1831² * H(exp V)` has `1831`-adic valuation at
least two. -/
theorem scaledPolynomialExp1831sq_derivative_hasPadicValAtLeast_two
    (P : Polynomial ℤ) (N : ℕ) :
    HasPadicValAtLeast 1831 2
      (formalDerivativeAtZero N
        (PowerSeries.C ((1831 : ℤ) ^ 2 : ℚ) * polynomialExp P)) := by
  rw [formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_polynomialExp_eq_intCast]
  have hp2 := HasPadicValAtLeast.primePow (p := 1831) 2
  have hmoment :=
    HasPadicValAtLeast.intCast (p := 1831) (polynomialMomentInt P N)
  convert hp2.mul hmoment using 1

/-- Since `P(1) ≡ 1 mod 1831²`, the positive relation polynomial is not
divisible by `1831` at `1`. -/
theorem oneThousandEightHundredThirtyOne_not_dvd_eval_one_positiveRelationPolynomial1831
    (b : SourceIndex 1831 → ℕ) :
    ¬(1831 : ℤ) ∣
      (positiveRelationPolynomial1831 b).eval 1 := by
  have hmod :=
    eval_one_positiveRelationPolynomial1831_mod_sq b
  have hzero :
      ((((positiveRelationPolynomial1831 b).eval 1 - 1 : ℤ)) :
        ZMod (1831 ^ 2)) = 0 := by
    push_cast
    rw [hmod]
    ring
  have hsquare :
      (((1831 ^ 2 : ℕ) : ℤ) ∣
        (positiveRelationPolynomial1831 b).eval 1 - 1) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hOneThousandEightHundredThirtyOne :
      (1831 : ℤ) ∣
        (positiveRelationPolynomial1831 b).eval 1 - 1 :=
    (by norm_num : (1831 : ℤ) ∣ ((1831 ^ 2 : ℕ) : ℤ)).trans hsquare
  intro heval
  have hone : (1831 : ℤ) ∣ 1 := by
    convert dvd_sub heval hOneThousandEightHundredThirtyOne using 1
    ring
  norm_num at hone

theorem constantCoeff_positiveRelationPolynomial1831_ne_zero
    (b : SourceIndex 1831 → ℕ) :
    PowerSeries.constantCoeff
      (polynomialExp (positiveRelationPolynomial1831 b)) ≠ 0 := by
  rw [constantCoeff_polynomialExp]
  exact_mod_cast
    (show (positiveRelationPolynomial1831 b).eval 1 ≠ 0 from
      fun hzero ↦
        oneThousandEightHundredThirtyOne_not_dvd_eval_one_positiveRelationPolynomial1831 b
          (hzero ▸ dvd_zero 1831))

theorem constantCoeff_positiveRelationPolynomial1831_padicVal_eq_zero
    (b : SourceIndex 1831 → ℕ) :
    padicValRat 1831
      (PowerSeries.constantCoeff
        (polynomialExp (positiveRelationPolynomial1831 b))) = 0 := by
  rw [constantCoeff_polynomialExp, padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd
      (oneThousandEightHundredThirtyOne_not_dvd_eval_one_positiveRelationPolynomial1831 b)]
  norm_num

/-! ## The specialized logarithmic derivative -/

omit [IsCyclotomicExtension {1831} ℚ K] in
/-- The polynomial-remainder and inverse-series recursion specialized to
one positive relation polynomial.

At the selected row `k`, the top derivative order is
`N = (2 * sourceNumber k) * 1831`. Thus `1831 ∣ N`, while the certified
source range gives `1830 ∤ N`, exactly the hypotheses of the generic
remainder theorem. -/
theorem positiveRelation_logarithmicDerivative_hasPadicValAtLeast_two
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1831)
    (b : SourceIndex 1831 → ℕ) (H : Polynomial ℤ) (C : ℤ)
    (hzero : Polynomial.aeval zeta
      (vanishingRelationPolynomial1831
        (positiveRelationPolynomial1831 b) 1 H C) = 0)
    (hsquare : (1831 : ℤ) ^ 2 ∣
      (vanishingRelationPolynomial1831
        (positiveRelationPolynomial1831 b) 1 H C).eval 1) :
    ∀ k : SourceIndex 1831,
      HasPadicValAtLeast 1831 2
        (formalDerivativeAtZero (sourceDerivativeOrder1831 k)
          (logarithmicDerivative
            (polynomialExp (positiveRelationPolynomial1831 b)))) := by
  let P := positiveRelationPolynomial1831 b
  let A := vanishingRelationPolynomial1831 P 1 H C
  have hzeroA : Polynomial.aeval zeta A = 0 := by
    simpa only [A, P] using hzero
  have hsquareA : (1831 : ℤ) ^ 2 ∣ A.eval 1 := by
    simpa only [A, P] using hsquare
  obtain ⟨V, b₁, hAseries⟩ :=
    exists_polynomialExp_eq_additiveRemainder
      (p := 1831) (by norm_num) hzeta A hzeroA hsquareA
  have hsource :
      polynomialExp P =
        PowerSeries.C (C : ℚ) +
          PowerSeries.C ((1831 : ℤ) ^ 2 : ℚ) * polynomialExp H +
          additiveRemainder 1831 V b₁ := by
    calc
      polynomialExp P =
          PowerSeries.C (C : ℚ) +
            PowerSeries.C ((1831 : ℤ) ^ 2 : ℚ) * polynomialExp H +
            polynomialExp A := by
              simpa only [A] using
                polynomialExp_vanishingRelationPolynomial1831 P H C
      _ = _ := by rw [hAseries]
  intro k
  let N := derivativeBernoulliIndex1831 k
  have hNpos : 0 < N := by
    simp [N, derivativeBernoulliIndex1831, sourceNumber]
  have hNgt : 1 < N := by
    simp only [N, derivativeBernoulliIndex1831, sourceNumber]
    omega
  have hNdiv : 1831 ∣ N := by
    refine ⟨2 * sourceNumber k, ?_⟩
    simp only [N, derivativeBernoulliIndex1831]
    ring
  have hNnot : ¬(1831 - 1) ∣ N := by
    simpa only [show 1831 - 1 = 1830 by norm_num, N] using
      oneThousandEightHundredThirty_not_dvd_derivativeBernoulliIndex1831 k
  have hlog :
      HasPadicValAtLeast 1831 2
        (formalDerivativeAtZero (N - 1)
          (logarithmicDerivative (polynomialExp P))) := by
    apply logarithmicDerivative_formalDerivative_hasPadicValAtLeast_two
      (p := 1831) (N := N) (by norm_num) hNpos
        (polynomialExp P)
    · simpa only [P] using
        constantCoeff_positiveRelationPolynomial1831_ne_zero b
    · simpa only [P] using
        constantCoeff_positiveRelationPolynomial1831_padicVal_eq_zero b
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
        scaledPolynomialExp1831sq_derivative_hasPadicValAtLeast_two H s
      have hremainder :=
        additiveRemainder_derivative_hasPadicValAtLeast_one
          (p := 1831) (by norm_num) s V b₁
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
        (scaledPolynomialExp1831sq_derivative_hasPadicValAtLeast_two H N).add
          (additiveRemainder_derivative_hasPadicValAtLeast_two
            (by norm_num) hNdiv hNgt hNnot V b₁)
  simpa only [N, sourceDerivativeOrder1831] using hlog

/-- The derivative of the logarithm of the positive relation polynomial is
exactly the existing exponent-weighted `relationDerivative1831`. -/
theorem relationDerivative1831_natCast_eq
    (b : SourceIndex 1831 → ℕ) (k : SourceIndex 1831) :
    relationDerivative1831 (fun i ↦ (b i : ℤ)) k =
      formalDerivativeAtZero (sourceDerivativeOrder1831 k)
        (logarithmicDerivative
          (polynomialExp (positiveRelationPolynomial1831 b))) := by
  rw [show polynomialExp (positiveRelationPolynomial1831 b) =
      polynomialExp1831 (positiveRelationPolynomial1831 b) by rfl]
  rw [formalDerivativeAtZero_positiveRelationPolynomial1831]
  rw [relationDerivative1831]
  apply Finset.sum_congr rfl
  intro i hi
  norm_cast

/-! ## Exact assembly premise -/

/-- Every deep positive relation in the 914 actual diagonal units has all
of Vandiver's selected relation derivatives divisible by `1831²`. -/
theorem positiveRelationDerivativeCongruences1831
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1831) :
    PositiveRelationDerivativeCongruences1831 hzeta := by
  intro v t b hvdeep hrel k
  obtain ⟨c, hdeep⟩ := hvdeep
  obtain ⟨H, hzero, hsquare⟩ :=
    exists_vanishingPositiveRelationPolynomial1831
      hzeta v c t b hdeep hrel
  rw [relationDerivative1831_natCast_eq]
  exact
    positiveRelation_logarithmicDerivative_hasPadicValAtLeast_two
      hzeta b H (c ^ (1831 * (1830 * t))) hzero hsquare k

end

end Fermat.OneThousandEightHundredThirtyOne.VandiverPositiveRelationDerivative
