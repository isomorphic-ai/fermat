/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# W1: relation-to-moment depth assembly

This layer joins the integral cyclotomic depth primitive to the polynomial
moment flow.  A deep numerator relation is corrected by an explicit
`p²`-multiple; the corrected relation has an exact prime-cyclotomic factor
and retains its `p²` value at one.  These are precisely the two inputs of
the nonlinear moment bridge.

The construction is generic over the prime and contains no
conductor-specific arithmetic.
-/
import Fermat.Conservation.Credit.DepthFlow
import Fermat.Conservation.Credit.NonlinearFlow
import Fermat.Conservation.Credit.RealHighFlow

open scoped NumberField

namespace Fermat.Conservation.Credit.RealFlow

open NumberField Polynomial

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

/-! ## Generator-derived integral node polynomials -/

/-- The canonical Teichmüller lift attached to a nonzero residue.  It is
formed from the indexed lift itself, before any quotient representative is
forgotten. -/
def teichLift (p : ℕ) (a : (ZMod p)ˣ) : ℕ :=
  (a : ZMod p).val ^ p

/-- The Teichmüller lift has the same reduction as its source node. -/
theorem natCast_teichLift {p : ℕ} [Fact p.Prime]
    (a : (ZMod p)ˣ) :
    (teichLift p a : ZMod p) = (a : ZMod p) := by
  simp [teichLift, ZMod.pow_card]

/-- Euler normalization modulo `p²` for the canonical lift. -/
theorem teichLift_pow_pred_modEq_one {p : ℕ} (hp : p.Prime)
    (a : (ZMod p)ˣ) :
    (teichLift p a) ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  have hcop : (a : ZMod p).val.Coprime (p ^ 2) :=
    (ZMod.val_coe_unit_coprime a).pow_right 2
  have heuler := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime_pow hp (by omega)] at heuler
  norm_num at heuler
  simpa only [teichLift, ← pow_mul] using heuler

/-- Integer divisibility form of Teichmüller normalization. -/
theorem prime_sq_dvd_teichLift_pow_pred_sub_one {p : ℕ}
    (hp : p.Prime) (a : (ZMod p)ˣ) :
    ((p : ℤ) ^ 2) ∣
      ((teichLift p a : ℤ) ^ (p - 1) - 1) := by
  have hnegative :
      ((p ^ 2 : ℕ) : ℤ) ∣
        1 - ((teichLift p a : ℕ) ^ (p - 1) : ℤ) :=
    (teichLift_pow_pred_modEq_one hp a).dvd
  have hpositive := dvd_neg.mpr hnegative
  simpa only [Nat.cast_pow, neg_sub] using hpositive

/-- Integral geometric-sum polynomial of length `r`. -/
noncomputable def geometricPolynomial (r : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range r, X ^ j

@[simp]
theorem geometricPolynomial_eval_one (r : ℕ) :
    (geometricPolynomial r).eval 1 = (r : ℤ) := by
  simp [geometricPolynomial]

/-- Polynomial representative of a folded real cyclotomic node.

The geometric sum uses the full Teichmüller lift.  Its residue is still
`a`, while its value at one now has the prime-square Euler normalization.
The monomial records the conjugation fold and has value one at `X = 1`. -/
noncomputable def foldedTeichNodePolynomial
    (p : ℕ) (a : (ZMod p)ˣ) : ℤ[X] :=
  X ^ (p + 1 - (a : ZMod p).val) *
    geometricPolynomial (teichLift p a) ^ 2

@[simp]
theorem foldedTeichNodePolynomial_eval_one
    (p : ℕ) (a : (ZMod p)ˣ) :
    (foldedTeichNodePolynomial p a).eval 1 =
      (teichLift p a : ℤ) ^ 2 := by
  simp [foldedTeichNodePolynomial]

/-- The normalized folded node is the `(p - 1)`st power. -/
noncomputable def normalizedFoldedNodePolynomial
    (p : ℕ) (a : (ZMod p)ˣ) : ℤ[X] :=
  foldedTeichNodePolynomial p a ^ (p - 1)

/-- Every normalized folded node has value one modulo `p²`. -/
theorem prime_sq_dvd_normalizedFoldedNodePolynomial_eval_one_sub_one
    {p : ℕ} (hp : p.Prime) (a : (ZMod p)ˣ) :
    ((p : ℤ) ^ 2) ∣
      (normalizedFoldedNodePolynomial p a).eval 1 - 1 := by
  have hmod := (teichLift_pow_pred_modEq_one hp a).pow 2
  have hnegative :
      ((p ^ 2 : ℕ) : ℤ) ∣
        1 - (((teichLift p a) ^ (p - 1)) ^ 2 : ℕ) :=
    hmod.dvd
  have hpositive := dvd_neg.mpr hnegative
  have hpositive' :
      ((p : ℤ) ^ 2) ∣
        (((teichLift p a : ℤ) ^ (p - 1)) ^ 2 - 1) := by
    simpa only [Nat.cast_pow, neg_sub] using hpositive
  convert hpositive' using 1
  simp only [normalizedFoldedNodePolynomial, Polynomial.eval_pow,
    foldedTeichNodePolynomial_eval_one, ← pow_mul]
  rw [Nat.mul_comm 2 (p - 1)]

/-- The normalized polynomial for the `i`th indexed real-residue lift. -/
noncomputable def normalizedNodePolynomial {p : ℕ}
    (data : RealGauge.RealGaugeData p) (i : ℕ) : ℤ[X] :=
  normalizedFoldedNodePolynomial p (data.nodeLift i)

/-- Positive part of an integral exponent. -/
def positiveExponent (z : ℤ) : ℕ :=
  z.toNat

/-- Negative part of an integral exponent. -/
def negativeExponent (z : ℤ) : ℕ :=
  (-z).toNat

/-- Numerator of the normalized generated-edge relation. -/
noncomputable def relationNumerator {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) : ℤ[X] :=
  ∏ i,
    normalizedNodePolynomial data (i.val + 1) ^
        positiveExponent (raw i) *
      normalizedNodePolynomial data i.val ^
        negativeExponent (raw i)

/-- Denominator of the normalized generated-edge relation. -/
noncomputable def relationDenominator {p : ℕ}
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) : ℤ[X] :=
  ∏ i,
    normalizedNodePolynomial data i.val ^
        positiveExponent (raw i) *
      normalizedNodePolynomial data (i.val + 1) ^
        negativeExponent (raw i)

private theorem dvd_pow_sub_one_of_dvd_sub_one
    {m x : ℤ} (n : ℕ) (h : m ∣ x - 1) :
    m ∣ x ^ n - 1 := by
  exact h.trans (by
    simpa using sub_dvd_pow_sub_pow x (1 : ℤ) n)

private theorem dvd_mul_sub_one_of_dvd_sub_one
    {m x y : ℤ} (hx : m ∣ x - 1) (hy : m ∣ y - 1) :
    m ∣ x * y - 1 := by
  have hxy : m ∣ x * (y - 1) + (x - 1) :=
    (dvd_mul_of_dvd_right hy x).add hx
  convert hxy using 1
  ring

private theorem dvd_finset_prod_sub_one_of_dvd_sub_one
    {ι : Type*} {m : ℤ} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, m ∣ f i - 1) :
    m ∣ (∏ i ∈ s, f i) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact dvd_mul_sub_one_of_dvd_sub_one
        (hf a (by simp)) (ih fun i hi ↦ hf i (by simp [hi]))

/-- Each indexed normalized node has value one modulo `p²`. -/
theorem prime_sq_dvd_normalizedNodePolynomial_eval_one_sub_one
    {p : ℕ} (data : RealGauge.RealGaugeData p) (i : ℕ) :
    ((p : ℤ) ^ 2) ∣
      (normalizedNodePolynomial data i).eval 1 - 1 := by
  exact
    prime_sq_dvd_normalizedFoldedNodePolynomial_eval_one_sub_one
      data.prime (data.nodeLift i)

/-- The generated numerator is automatically one modulo `p²` at
`X = 1`. -/
theorem prime_sq_dvd_relationNumerator_eval_one_sub_one
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    ((p : ℤ) ^ 2) ∣ (relationNumerator data raw).eval 1 - 1 := by
  rw [relationNumerator, Polynomial.eval_prod]
  apply dvd_finset_prod_sub_one_of_dvd_sub_one
  intro i _
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow]
  apply dvd_mul_sub_one_of_dvd_sub_one
  · exact dvd_pow_sub_one_of_dvd_sub_one _
      (prime_sq_dvd_normalizedNodePolynomial_eval_one_sub_one
        data (i.val + 1))
  · exact dvd_pow_sub_one_of_dvd_sub_one _
      (prime_sq_dvd_normalizedNodePolynomial_eval_one_sub_one
        data i.val)

/-- The generated denominator is automatically one modulo `p²` at
`X = 1`. -/
theorem prime_sq_dvd_relationDenominator_eval_one_sub_one
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    ((p : ℤ) ^ 2) ∣ (relationDenominator data raw).eval 1 - 1 := by
  rw [relationDenominator, Polynomial.eval_prod]
  apply dvd_finset_prod_sub_one_of_dvd_sub_one
  intro i _
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow]
  apply dvd_mul_sub_one_of_dvd_sub_one
  · exact dvd_pow_sub_one_of_dvd_sub_one _
      (prime_sq_dvd_normalizedNodePolynomial_eval_one_sub_one
        data i.val)
  · exact dvd_pow_sub_one_of_dvd_sub_one _
      (prime_sq_dvd_normalizedNodePolynomial_eval_one_sub_one
        data (i.val + 1))

/-- The numerator-minus-denominator relation has the value-at-one layer
required by the nonlinear bridge, without any per-prime certificate. -/
theorem prime_sq_dvd_relation_difference_eval_one
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    ((p : ℤ) ^ 2) ∣
      (relationNumerator data raw -
        relationDenominator data raw).eval 1 := by
  rw [Polynomial.eval_sub]
  have hnum :=
    prime_sq_dvd_relationNumerator_eval_one_sub_one data raw
  have hden :=
    prime_sq_dvd_relationDenominator_eval_one_sub_one data raw
  convert hnum.sub hden using 1
  ring

/-- The normalized denominator has unit constant jet modulo `p²`. -/
theorem relationDenominator_moment_zero_isUnit
    {p : ℕ} (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ) :
    IsUnit
      (Flow.momentModPrimeSq p 0 (relationDenominator data raw)) := by
  have hzero :
      (((relationDenominator data raw).eval 1 - 1 : ℤ) :
          ZMod (p ^ 2)) = 0 :=
    Flow.intCast_eq_zero_of_prime_sq_dvd
      (prime_sq_dvd_relationDenominator_eval_one_sub_one data raw)
  have hone :
      (((relationDenominator data raw).eval 1 : ℤ) :
          ZMod (p ^ 2)) = 1 := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_sub, Int.cast_one] using hzero
  rw [Flow.momentModPrimeSq,
    Flow.exponentialMoment_zero_eq_eval_one, hone]
  exact isUnit_one

/-- A depth-corrected polynomial has both forms needed downstream: an exact
prime-cyclotomic factor and a prime-square-divisible value at one. -/
theorem exists_moment_ready_correction_of_depth
    (A : ℤ[X])
    (hdepth :
      ((1 : 𝓞 K) - hζ.toInteger) ^ (2 * p) ∣
        Polynomial.eval₂ (algebraMap ℤ (𝓞 K)) hζ.toInteger A)
    (heval : ((p : ℤ) ^ 2) ∣ A.eval 1) :
    ∃ H B : ℤ[X],
      A - Polynomial.C ((p : ℤ) ^ 2) * H =
        Polynomial.cyclotomic p ℤ * B ∧
      ((p : ℤ) ^ 2) ∣
        (A - Polynomial.C ((p : ℤ) ^ 2) * H).eval 1 := by
  obtain ⟨H, hdvd⟩ :=
    Flow.exists_cyclotomic_dvd_correction_of_depth hζ A hdepth
  obtain ⟨B, hfactor⟩ := hdvd
  refine ⟨H, B, hfactor, ?_⟩
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  exact heval.sub (dvd_mul_right ((p : ℤ) ^ 2) (H.eval 1))

/-- Relation form of `exists_moment_ready_correction_of_depth`.

The correction is absorbed into the numerator.  Thus the denominator and
the rational scalar are unchanged, while the numerator difference becomes
an exact cyclotomic multiple suitable for `NonlinearFlow`. -/
theorem exists_moment_ready_relation_of_depth
    (P Q : ℤ[X]) (c : ℤ)
    (hdepth :
      ((1 : 𝓞 K) - hζ.toInteger) ^ (2 * p) ∣
        Polynomial.eval₂ (algebraMap ℤ (𝓞 K)) hζ.toInteger
          (P - Polynomial.C c * Q))
    (heval :
      ((p : ℤ) ^ 2) ∣ (P - Polynomial.C c * Q).eval 1) :
    ∃ H B : ℤ[X],
      (P - Polynomial.C ((p : ℤ) ^ 2) * H) -
          Polynomial.C c * Q =
        Polynomial.cyclotomic p ℤ * B ∧
      ((p : ℤ) ^ 2) ∣
        ((P - Polynomial.C ((p : ℤ) ^ 2) * H) -
          Polynomial.C c * Q).eval 1 := by
  obtain ⟨H, B, hfactor, heval'⟩ :=
    exists_moment_ready_correction_of_depth hζ
      (P - Polynomial.C c * Q) hdepth heval
  refine ⟨H, B, ?_, ?_⟩
  · calc
      (P - Polynomial.C ((p : ℤ) ^ 2) * H) -
            Polynomial.C c * Q =
          (P - Polynomial.C c * Q) -
            Polynomial.C ((p : ℤ) ^ 2) * H := by ring
      _ = Polynomial.cyclotomic p ℤ * B := hfactor
  · have heq :
        (P - Polynomial.C ((p : ℤ) ^ 2) * H) -
            Polynomial.C c * Q =
          (P - Polynomial.C c * Q) -
            Polynomial.C ((p : ℤ) ^ 2) * H := by
      ring
    rw [heq]
    exact heval'

/-- A deep generated relation is converted mechanically into the exact
factorization and value-at-one layer consumed by `NonlinearFlow`. -/
theorem exists_moment_ready_generated_relation_of_depth
    (data : RealGauge.RealGaugeData p)
    (raw : Fin data.rank → ℤ)
    (hdepth :
      ((1 : 𝓞 K) - hζ.toInteger) ^ (2 * p) ∣
        Polynomial.eval₂ (algebraMap ℤ (𝓞 K)) hζ.toInteger
          (relationNumerator data raw -
            relationDenominator data raw)) :
    ∃ H B : ℤ[X],
      (relationNumerator data raw -
          Polynomial.C ((p : ℤ) ^ 2) * H) -
          relationDenominator data raw =
        Polynomial.cyclotomic p ℤ * B ∧
      ((p : ℤ) ^ 2) ∣
        ((relationNumerator data raw -
          Polynomial.C ((p : ℤ) ^ 2) * H) -
          relationDenominator data raw).eval 1 := by
  simpa using
    exists_moment_ready_relation_of_depth hζ
      (relationNumerator data raw) (relationDenominator data raw) 1
      (by simpa using hdepth)
      (by
        simpa using prime_sq_dvd_relation_difference_eval_one data raw)

end Fermat.Conservation.Credit.RealFlow
