import Fermat.Irregular.VandiverLogDerivativeValuation
import Fermat.FiftyNine.VandiverDeepPolynomial
import Fermat.FiftyNine.VandiverNormalizedRelationDerivative

/-!
# Vandiver's positive-relation derivative congruence at 59

This file completes the polynomial-remainder calculation for a relation
with natural exponents in the twenty-eight actual diagonal units at exponent
`59`.

A deep relation first gives the integer polynomial

`A = P - C - 59² H`

from `VandiverDeepPolynomial`, with `A(zeta) = 0` and `59² ∣ A(1)`.
After substituting `W = exp V`, this becomes

`P(exp V) = C + 59² H(exp V) + A(exp V)`.

The generic remainder theorem supplies valuation at least one for every
derivative of `A(exp V)` and valuation at least two at Vandiver's selected
orders.  The `59² H(exp V)` term has valuation at least two at every order.
Moreover, `P(1) ≡ 1 mod 59²`, so the source series has a nonzero
valuation-zero constant coefficient.  The inverse-series recursion in
`VandiverLogDerivativeValuation` can therefore be applied to its
logarithmic derivative.

Finally, `VandiverPolynomialUnits` identifies this logarithmic derivative
with `relationDerivative59`.  The endpoint is the exact
`PositiveRelationDerivativeCongruences59` premise consumed by
`VandiverLemmaTwoAssembly`.
-/

open scoped BigOperators NumberField

namespace Fermat.FiftyNine.VandiverPositiveRelationDerivative

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverRemainderDerivative
open Fermat.Irregular.VandiverLogDerivativeValuation
open Fermat.Irregular.Voronoi
open Fermat.FiftyNine.VandiverDiagonalUnits
open Fermat.FiftyNine.VandiverDerivativeValuation
open Fermat.FiftyNine.VandiverDiagonalDerivative
open Fermat.FiftyNine.VandiverPolynomialUnits
open Fermat.FiftyNine.VandiverDeepPolynomial
open Fermat.FiftyNine.VandiverNormalizedRelationDerivative

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-! ## The positive vanishing polynomial -/

/-- Specialization of the deep polynomial construction to natural
exponents.  The negative relation polynomial becomes `1`, leaving the
source's positive polynomial in the exact form `P - C - 59² H`. -/
theorem exists_vanishingPositiveRelationPolynomial59
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 59)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (b : SourceIndex 59 → ℕ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 118 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 59)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit59 hzeta i ^ b i) :
    ∃ H : Polynomial ℤ,
      let P := positiveRelationPolynomial59 b
      let C : ℤ := c ^ (59 * (58 * t))
      let A := vanishingRelationPolynomial59 P 1 H C
      Polynomial.aeval zeta A = 0 ∧
        (59 : ℤ) ^ 2 ∣ A.eval 1 := by
  have hrelZ : u ^ t =
      ∏ i, diagonalVandiverUnit59 hzeta i ^ (b i : ℤ) := by
    simpa only [zpow_natCast] using hrel
  obtain ⟨H, hzero, hsquare⟩ :=
    exists_vanishingRelationPolynomial59 hzeta u c t
      (fun i ↦ (b i : ℤ)) hdeep hrelZ
  refine ⟨H, ?_, ?_⟩
  · simpa [positiveRelationPolynomial59] using hzero
  · simpa [positiveRelationPolynomial59] using hsquare

/-- Exponential substitution turns `A = P - C - 59² H` into the additive
source decomposition used in the derivative recursion. -/
theorem polynomialExp_vanishingRelationPolynomial59
    (P H : Polynomial ℤ) (C : ℤ) :
    polynomialExp P =
      PowerSeries.C (C : ℚ) +
        PowerSeries.C ((59 : ℤ) ^ 2 : ℚ) * polynomialExp H +
        polynomialExp (vanishingRelationPolynomial59 P 1 H C) := by
  rw [vanishingRelationPolynomial59]
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

/-- Every derivative of `59² * H(exp V)` has `59`-adic valuation at
least two. -/
theorem scaledPolynomialExp59sq_derivative_hasPadicValAtLeast_two
    (P : Polynomial ℤ) (N : ℕ) :
    HasPadicValAtLeast 59 2
      (formalDerivativeAtZero N
        (PowerSeries.C ((59 : ℤ) ^ 2 : ℚ) * polynomialExp P)) := by
  rw [formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_polynomialExp_eq_intCast]
  have hp2 := HasPadicValAtLeast.primePow (p := 59) 2
  have hmoment :=
    HasPadicValAtLeast.intCast (p := 59) (polynomialMomentInt P N)
  convert hp2.mul hmoment using 1

/-- Since `P(1) ≡ 1 mod 59²`, the positive relation polynomial is not
divisible by `59` at `1`. -/
theorem fiftyNine_not_dvd_eval_one_positiveRelationPolynomial59
    (b : SourceIndex 59 → ℕ) :
    ¬(59 : ℤ) ∣
      (positiveRelationPolynomial59 b).eval 1 := by
  have hmod :=
    eval_one_positiveRelationPolynomial59_mod_sq b
  have hzero :
      ((((positiveRelationPolynomial59 b).eval 1 - 1 : ℤ)) :
        ZMod (59 ^ 2)) = 0 := by
    push_cast
    rw [hmod]
    ring
  have hsquare :
      (((59 ^ 2 : ℕ) : ℤ) ∣
        (positiveRelationPolynomial59 b).eval 1 - 1) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hfiftyNine :
      (59 : ℤ) ∣
        (positiveRelationPolynomial59 b).eval 1 - 1 :=
    (by norm_num : (59 : ℤ) ∣ ((59 ^ 2 : ℕ) : ℤ)).trans hsquare
  intro heval
  have hone : (59 : ℤ) ∣ 1 := by
    convert dvd_sub heval hfiftyNine using 1
    ring
  norm_num at hone

theorem constantCoeff_positiveRelationPolynomial59_ne_zero
    (b : SourceIndex 59 → ℕ) :
    PowerSeries.constantCoeff
      (polynomialExp (positiveRelationPolynomial59 b)) ≠ 0 := by
  rw [constantCoeff_polynomialExp]
  exact_mod_cast
    (show (positiveRelationPolynomial59 b).eval 1 ≠ 0 from
      fun hzero ↦
        fiftyNine_not_dvd_eval_one_positiveRelationPolynomial59 b
          (hzero ▸ dvd_zero 59))

theorem constantCoeff_positiveRelationPolynomial59_padicVal_eq_zero
    (b : SourceIndex 59 → ℕ) :
    padicValRat 59
      (PowerSeries.constantCoeff
        (polynomialExp (positiveRelationPolynomial59 b))) = 0 := by
  rw [constantCoeff_polynomialExp, padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd
      (fiftyNine_not_dvd_eval_one_positiveRelationPolynomial59 b)]
  norm_num

/-! ## The specialized logarithmic derivative -/

omit [IsCyclotomicExtension {59} ℚ K] in
/-- The polynomial-remainder and inverse-series recursion specialized to
one positive relation polynomial.

At the selected row `k`, the top derivative order is
`N = (2 * sourceNumber k) * 59`.  Thus `59 ∣ N`, while the certified
source range gives `58 ∤ N`, exactly the hypotheses of the generic
remainder theorem. -/
theorem positiveRelation_logarithmicDerivative_hasPadicValAtLeast_two
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 59)
    (b : SourceIndex 59 → ℕ) (H : Polynomial ℤ) (C : ℤ)
    (hzero : Polynomial.aeval zeta
      (vanishingRelationPolynomial59
        (positiveRelationPolynomial59 b) 1 H C) = 0)
    (hsquare : (59 : ℤ) ^ 2 ∣
      (vanishingRelationPolynomial59
        (positiveRelationPolynomial59 b) 1 H C).eval 1) :
    ∀ k : SourceIndex 59,
      HasPadicValAtLeast 59 2
        (formalDerivativeAtZero (sourceDerivativeOrder59 k)
          (logarithmicDerivative
            (polynomialExp (positiveRelationPolynomial59 b)))) := by
  let P := positiveRelationPolynomial59 b
  let A := vanishingRelationPolynomial59 P 1 H C
  have hzeroA : Polynomial.aeval zeta A = 0 := by
    simpa only [A, P] using hzero
  have hsquareA : (59 : ℤ) ^ 2 ∣ A.eval 1 := by
    simpa only [A, P] using hsquare
  obtain ⟨V, b₁, hAseries⟩ :=
    exists_polynomialExp_eq_additiveRemainder
      (p := 59) (by norm_num) hzeta A hzeroA hsquareA
  have hsource :
      polynomialExp P =
        PowerSeries.C (C : ℚ) +
          PowerSeries.C ((59 : ℤ) ^ 2 : ℚ) * polynomialExp H +
          additiveRemainder 59 V b₁ := by
    calc
      polynomialExp P =
          PowerSeries.C (C : ℚ) +
            PowerSeries.C ((59 : ℤ) ^ 2 : ℚ) * polynomialExp H +
            polynomialExp A := by
              simpa only [A] using
                polynomialExp_vanishingRelationPolynomial59 P H C
      _ = _ := by rw [hAseries]
  intro k
  let N := derivativeBernoulliIndex59 k
  have hNpos : 0 < N := by
    simp [N, derivativeBernoulliIndex59, sourceNumber]
  have hNgt : 1 < N := by
    simp only [N, derivativeBernoulliIndex59, sourceNumber]
    omega
  have hNdiv : 59 ∣ N := by
    refine ⟨2 * sourceNumber k, ?_⟩
    simp only [N, derivativeBernoulliIndex59]
    ring
  have hNnot : ¬(59 - 1) ∣ N := by
    simpa only [show 59 - 1 = 58 by norm_num, N] using
      fiftyEight_not_dvd_derivativeBernoulliIndex59 k
  have hlog :
      HasPadicValAtLeast 59 2
        (formalDerivativeAtZero (N - 1)
          (logarithmicDerivative (polynomialExp P))) := by
    apply logarithmicDerivative_formalDerivative_hasPadicValAtLeast_two
      (p := 59) (N := N) (by norm_num) hNpos
        (polynomialExp P)
    · simpa only [P] using
        constantCoeff_positiveRelationPolynomial59_ne_zero b
    · simpa only [P] using
        constantCoeff_positiveRelationPolynomial59_padicVal_eq_zero b
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
        scaledPolynomialExp59sq_derivative_hasPadicValAtLeast_two H s
      have hremainder :=
        additiveRemainder_derivative_hasPadicValAtLeast_one
          (p := 59) (by norm_num) s V b₁
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
        (scaledPolynomialExp59sq_derivative_hasPadicValAtLeast_two H N).add
          (additiveRemainder_derivative_hasPadicValAtLeast_two
            (by norm_num) hNdiv hNgt hNnot V b₁)
  simpa only [N, sourceDerivativeOrder59] using hlog

/-- The derivative of the logarithm of the positive relation polynomial is
exactly the existing exponent-weighted `relationDerivative59`. -/
theorem relationDerivative59_natCast_eq
    (b : SourceIndex 59 → ℕ) (k : SourceIndex 59) :
    relationDerivative59 (fun i ↦ (b i : ℤ)) k =
      formalDerivativeAtZero (sourceDerivativeOrder59 k)
        (logarithmicDerivative
          (polynomialExp (positiveRelationPolynomial59 b))) := by
  rw [show polynomialExp (positiveRelationPolynomial59 b) =
      polynomialExp59 (positiveRelationPolynomial59 b) by rfl]
  rw [formalDerivativeAtZero_positiveRelationPolynomial59]
  rw [relationDerivative59]
  apply Finset.sum_congr rfl
  intro i hi
  norm_cast

/-! ## Exact assembly premise -/

/-- Every deep positive relation in the twenty-eight actual diagonal units
has all of Vandiver's selected relation derivatives divisible by `59²`.

This is the exact final premise expected by
`VandiverNormalizedRelationDerivative` and `VandiverLemmaTwoAssembly`. -/
theorem positiveRelationDerivativeCongruences59
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 59) :
    PositiveRelationDerivativeCongruences59 hzeta := by
  intro v t b hvdeep hrel k
  obtain ⟨c, hdeep⟩ := hvdeep
  obtain ⟨H, hzero, hsquare⟩ :=
    exists_vanishingPositiveRelationPolynomial59
      hzeta v c t b hdeep hrel
  rw [relationDerivative59_natCast_eq]
  exact
    positiveRelation_logarithmicDerivative_hasPadicValAtLeast_two
      hzeta b H (c ^ (59 * (58 * t))) hzero hsquare k

end

end Fermat.FiftyNine.VandiverPositiveRelationDerivative
