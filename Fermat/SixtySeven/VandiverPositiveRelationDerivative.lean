import Fermat.Irregular.VandiverLogDerivativeValuation
import Fermat.SixtySeven.VandiverDeepPolynomial
import Fermat.SixtySeven.VandiverNormalizedRelationDerivative

/-!
# Vandiver's positive-relation derivative congruence at 67

This file completes the polynomial-remainder calculation for a relation
with natural exponents in the thirty-two actual diagonal units at exponent
`67`.

A deep relation first gives the integer polynomial

`A = P - C - 67² H`

from `VandiverDeepPolynomial`, with `A(zeta) = 0` and `67² ∣ A(1)`.
After substituting `W = exp V`, this becomes

`P(exp V) = C + 67² H(exp V) + A(exp V)`.

The generic remainder theorem supplies valuation at least one for every
derivative of `A(exp V)` and valuation at least two at Vandiver's selected
orders.  The `67² H(exp V)` term has valuation at least two at every order.
Moreover, `P(1) ≡ 1 mod 67²`, so the source series has a nonzero
valuation-zero constant coefficient.  The inverse-series recursion in
`VandiverLogDerivativeValuation` can therefore be applied to its
logarithmic derivative.

Finally, `VandiverPolynomialUnits` identifies this logarithmic derivative
with `relationDerivative67`.  The endpoint is the exact
`PositiveRelationDerivativeCongruences67` premise consumed by
`VandiverLemmaTwoAssembly`.
-/

open scoped BigOperators NumberField

namespace Fermat.SixtySeven.VandiverPositiveRelationDerivative

noncomputable section

open Polynomial PowerSeries
open Fermat.Irregular
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverLogDerivative
open Fermat.Irregular.VandiverPowerSeriesLog
open Fermat.Irregular.VandiverRemainderDerivative
open Fermat.Irregular.VandiverLogDerivativeValuation
open Fermat.Irregular.Voronoi
open Fermat.SixtySeven.VandiverDiagonalUnits
open Fermat.SixtySeven.VandiverDerivativeValuation
open Fermat.SixtySeven.VandiverDiagonalDerivative
open Fermat.SixtySeven.VandiverPolynomialUnits
open Fermat.SixtySeven.VandiverDeepPolynomial
open Fermat.SixtySeven.VandiverNormalizedRelationDerivative

local instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {67} ℚ K]

/-! ## The positive vanishing polynomial -/

/-- Specialization of the deep polynomial construction to natural
exponents.  The negative relation polynomial becomes `1`, leaving the
source's positive polynomial in the exact form `P - C - 67² H`. -/
theorem exists_vanishingPositiveRelationPolynomial67
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (b : SourceIndex 67 → ℕ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 134 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 67)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit67 hzeta i ^ b i) :
    ∃ H : Polynomial ℤ,
      let P := positiveRelationPolynomial67 b
      let C : ℤ := c ^ (67 * (66 * t))
      let A := vanishingRelationPolynomial67 P 1 H C
      Polynomial.aeval zeta A = 0 ∧
        (67 : ℤ) ^ 2 ∣ A.eval 1 := by
  have hrelZ : u ^ t =
      ∏ i, diagonalVandiverUnit67 hzeta i ^ (b i : ℤ) := by
    simpa only [zpow_natCast] using hrel
  obtain ⟨H, hzero, hsquare⟩ :=
    exists_vanishingRelationPolynomial67 hzeta u c t
      (fun i ↦ (b i : ℤ)) hdeep hrelZ
  refine ⟨H, ?_, ?_⟩
  · simpa [positiveRelationPolynomial67] using hzero
  · simpa [positiveRelationPolynomial67] using hsquare

/-- Exponential substitution turns `A = P - C - 67² H` into the additive
source decomposition used in the derivative recursion. -/
theorem polynomialExp_vanishingRelationPolynomial67
    (P H : Polynomial ℤ) (C : ℤ) :
    polynomialExp P =
      PowerSeries.C (C : ℚ) +
        PowerSeries.C ((67 : ℤ) ^ 2 : ℚ) * polynomialExp H +
        polynomialExp (vanishingRelationPolynomial67 P 1 H C) := by
  rw [vanishingRelationPolynomial67]
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

/-- Every derivative of `67² * H(exp V)` has `67`-adic valuation at
least two. -/
theorem scaledPolynomialExp67sq_derivative_hasPadicValAtLeast_two
    (P : Polynomial ℤ) (N : ℕ) :
    HasPadicValAtLeast 67 2
      (formalDerivativeAtZero N
        (PowerSeries.C ((67 : ℤ) ^ 2 : ℚ) * polynomialExp P)) := by
  rw [formalDerivativeAtZero_C_mul,
    formalDerivativeAtZero_polynomialExp_eq_intCast]
  have hp2 := HasPadicValAtLeast.primePow (p := 67) 2
  have hmoment :=
    HasPadicValAtLeast.intCast (p := 67) (polynomialMomentInt P N)
  convert hp2.mul hmoment using 1

/-- Since `P(1) ≡ 1 mod 67²`, the positive relation polynomial is not
divisible by `67` at `1`. -/
theorem sixtySeven_not_dvd_eval_one_positiveRelationPolynomial67
    (b : SourceIndex 67 → ℕ) :
    ¬(67 : ℤ) ∣
      (positiveRelationPolynomial67 b).eval 1 := by
  have hmod :=
    eval_one_positiveRelationPolynomial67_mod_sq b
  have hzero :
      ((((positiveRelationPolynomial67 b).eval 1 - 1 : ℤ)) :
        ZMod (67 ^ 2)) = 0 := by
    push_cast
    rw [hmod]
    ring
  have hsquare :
      (((67 ^ 2 : ℕ) : ℤ) ∣
        (positiveRelationPolynomial67 b).eval 1 - 1) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hsixtySeven :
      (67 : ℤ) ∣
        (positiveRelationPolynomial67 b).eval 1 - 1 :=
    (by norm_num : (67 : ℤ) ∣ ((67 ^ 2 : ℕ) : ℤ)).trans hsquare
  intro heval
  have hone : (67 : ℤ) ∣ 1 := by
    convert dvd_sub heval hsixtySeven using 1
    ring
  norm_num at hone

theorem constantCoeff_positiveRelationPolynomial67_ne_zero
    (b : SourceIndex 67 → ℕ) :
    PowerSeries.constantCoeff
      (polynomialExp (positiveRelationPolynomial67 b)) ≠ 0 := by
  rw [constantCoeff_polynomialExp]
  exact_mod_cast
    (show (positiveRelationPolynomial67 b).eval 1 ≠ 0 from
      fun hzero ↦
        sixtySeven_not_dvd_eval_one_positiveRelationPolynomial67 b
          (hzero ▸ dvd_zero 67))

theorem constantCoeff_positiveRelationPolynomial67_padicVal_eq_zero
    (b : SourceIndex 67 → ℕ) :
    padicValRat 67
      (PowerSeries.constantCoeff
        (polynomialExp (positiveRelationPolynomial67 b))) = 0 := by
  rw [constantCoeff_polynomialExp, padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd
      (sixtySeven_not_dvd_eval_one_positiveRelationPolynomial67 b)]
  norm_num

/-! ## The specialized logarithmic derivative -/

omit [IsCyclotomicExtension {67} ℚ K] in
/-- The polynomial-remainder and inverse-series recursion specialized to
one positive relation polynomial.

At the selected row `k`, the top derivative order is
`N = (2 * sourceNumber k) * 67`.  Thus `67 ∣ N`, while the certified
source range gives `66 ∤ N`, exactly the hypotheses of the generic
remainder theorem. -/
theorem positiveRelation_logarithmicDerivative_hasPadicValAtLeast_two
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67)
    (b : SourceIndex 67 → ℕ) (H : Polynomial ℤ) (C : ℤ)
    (hzero : Polynomial.aeval zeta
      (vanishingRelationPolynomial67
        (positiveRelationPolynomial67 b) 1 H C) = 0)
    (hsquare : (67 : ℤ) ^ 2 ∣
      (vanishingRelationPolynomial67
        (positiveRelationPolynomial67 b) 1 H C).eval 1) :
    ∀ k : SourceIndex 67,
      HasPadicValAtLeast 67 2
        (formalDerivativeAtZero (sourceDerivativeOrder67 k)
          (logarithmicDerivative
            (polynomialExp (positiveRelationPolynomial67 b)))) := by
  let P := positiveRelationPolynomial67 b
  let A := vanishingRelationPolynomial67 P 1 H C
  have hzeroA : Polynomial.aeval zeta A = 0 := by
    simpa only [A, P] using hzero
  have hsquareA : (67 : ℤ) ^ 2 ∣ A.eval 1 := by
    simpa only [A, P] using hsquare
  obtain ⟨V, b₁, hAseries⟩ :=
    exists_polynomialExp_eq_additiveRemainder
      (p := 67) (by norm_num) hzeta A hzeroA hsquareA
  have hsource :
      polynomialExp P =
        PowerSeries.C (C : ℚ) +
          PowerSeries.C ((67 : ℤ) ^ 2 : ℚ) * polynomialExp H +
          additiveRemainder 67 V b₁ := by
    calc
      polynomialExp P =
          PowerSeries.C (C : ℚ) +
            PowerSeries.C ((67 : ℤ) ^ 2 : ℚ) * polynomialExp H +
            polynomialExp A := by
              simpa only [A] using
                polynomialExp_vanishingRelationPolynomial67 P H C
      _ = _ := by rw [hAseries]
  intro k
  let N := derivativeBernoulliIndex67 k
  have hNpos : 0 < N := by
    simp [N, derivativeBernoulliIndex67, sourceNumber]
  have hNgt : 1 < N := by
    simp only [N, derivativeBernoulliIndex67, sourceNumber]
    omega
  have hNdiv : 67 ∣ N := by
    refine ⟨2 * sourceNumber k, ?_⟩
    simp only [N, derivativeBernoulliIndex67]
    ring
  have hNnot : ¬(67 - 1) ∣ N := by
    simpa only [show 67 - 1 = 66 by norm_num, N] using
      sixtySix_not_dvd_derivativeBernoulliIndex67 k
  have hlog :
      HasPadicValAtLeast 67 2
        (formalDerivativeAtZero (N - 1)
          (logarithmicDerivative (polynomialExp P))) := by
    apply logarithmicDerivative_formalDerivative_hasPadicValAtLeast_two
      (p := 67) (N := N) (by norm_num) hNpos
        (polynomialExp P)
    · simpa only [P] using
        constantCoeff_positiveRelationPolynomial67_ne_zero b
    · simpa only [P] using
        constantCoeff_positiveRelationPolynomial67_padicVal_eq_zero b
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
        scaledPolynomialExp67sq_derivative_hasPadicValAtLeast_two H s
      have hremainder :=
        additiveRemainder_derivative_hasPadicValAtLeast_one
          (p := 67) (by norm_num) s V b₁
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
        (scaledPolynomialExp67sq_derivative_hasPadicValAtLeast_two H N).add
          (additiveRemainder_derivative_hasPadicValAtLeast_two
            (by norm_num) hNdiv hNgt hNnot V b₁)
  simpa only [N, sourceDerivativeOrder67] using hlog

/-- The derivative of the logarithm of the positive relation polynomial is
exactly the existing exponent-weighted `relationDerivative67`. -/
theorem relationDerivative67_natCast_eq
    (b : SourceIndex 67 → ℕ) (k : SourceIndex 67) :
    relationDerivative67 (fun i ↦ (b i : ℤ)) k =
      formalDerivativeAtZero (sourceDerivativeOrder67 k)
        (logarithmicDerivative
          (polynomialExp (positiveRelationPolynomial67 b))) := by
  rw [show polynomialExp (positiveRelationPolynomial67 b) =
      polynomialExp67 (positiveRelationPolynomial67 b) by rfl]
  rw [formalDerivativeAtZero_positiveRelationPolynomial67]
  rw [relationDerivative67]
  apply Finset.sum_congr rfl
  intro i hi
  norm_cast

/-! ## Exact assembly premise -/

/-- Every deep positive relation in the thirty-two actual diagonal units
has all of Vandiver's selected relation derivatives divisible by `67²`.

This is the exact final premise expected by
`VandiverNormalizedRelationDerivative` and `VandiverLemmaTwoAssembly`. -/
theorem positiveRelationDerivativeCongruences67
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67) :
    PositiveRelationDerivativeCongruences67 hzeta := by
  intro v t b hvdeep hrel k
  obtain ⟨c, hdeep⟩ := hvdeep
  obtain ⟨H, hzero, hsquare⟩ :=
    exists_vanishingPositiveRelationPolynomial67
      hzeta v c t b hdeep hrel
  rw [relationDerivative67_natCast_eq]
  exact
    positiveRelation_logarithmicDerivative_hasPadicValAtLeast_two
      hzeta b H (c ^ (67 * (66 * t))) hzero hsquare k

end

end Fermat.SixtySeven.VandiverPositiveRelationDerivative
