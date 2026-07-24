import Fermat.Irregular.VandiverHistoricalPrime

/-!
# Prime-generic quadratic form of historical equation (8a)

For an odd exponent `p = 2 * r + 1`, the distinguished equation-(8a)
factor has exponent `p * m - r`.  Squaring it changes that exponent into

`2 * (p * m - r) = p * (2 * m - 1) + 1`.

The extra factor is precisely Vandiver's real uniformizer `κ`; the
remaining factors form a `p`-th power.  This is the third quadratic input
to the universal equation-(10a) elimination.
-/

namespace Fermat.Irregular.VandiverHistoricalQuadraticPrime

open scoped NumberField

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime

noncomputable section

variable {K : Type} {p r : ℕ} [Fact p.Prime]
  [Field K] [NumberField K]

omit [NumberField K] in
/-- Squaring historical equation (8a), uniformly for every odd prime
written as `p = 2 * r + 1`. -/
lemma historicalEquationEightA_quadratic
    (hr : p = 2 * r + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (m : ℕ) (hm : 1 < m)
    (ω θ rhoZero : 𝓞 K) (etaZero : (𝓞 K)ˣ)
    (hzero :
      ω + θ =
        etaZero * kappa hζ ^ (p * m - r) * rhoZero ^ p) :
    ω ^ 2 + 2 * (ω * θ) + θ ^ 2 =
      kappa hζ *
        ((etaZero ^ 2 : (𝓞 K)ˣ) *
          (kappa hζ ^ (2 * m - 1) * rhoZero ^ 2) ^ p) := by
  have hsquare := congrArg (fun x : 𝓞 K ↦ x ^ 2) hzero
  have hexp :
      (p * m - r) * 2 =
        (2 * m - 1) * p + 1 := by
    have hpm : p ≤ p * m :=
      Nat.le_mul_of_pos_right p (by omega)
    simp only [Nat.sub_mul, one_mul]
    have hleft : p * m * 2 = 2 * (p * m) := by ring
    have hsub : r * 2 = 2 * r := by ring
    have hright : 2 * m * p = 2 * (p * m) := by ring
    rw [hleft, hsub, hright]
    omega
  calc
    ω ^ 2 + 2 * (ω * θ) + θ ^ 2 =
        (ω + θ) ^ 2 := by ring
    _ = ((etaZero : 𝓞 K) *
          kappa hζ ^ (p * m - r) * rhoZero ^ p) ^ 2 := hsquare
    _ = kappa hζ *
        ((etaZero ^ 2 : (𝓞 K)ˣ) *
          (kappa hζ ^ (2 * m - 1) * rhoZero ^ 2) ^ p) := by
      simp only [mul_pow, Units.val_pow_eq_pow_val, ← pow_mul]
      rw [hexp, pow_succ']
      ring

end

end Fermat.Irregular.VandiverHistoricalQuadraticPrime
