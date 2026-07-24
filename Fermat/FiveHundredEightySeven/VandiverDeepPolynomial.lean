import Fermat.Irregular.VandiverPolynomialRemainder
import Fermat.Irregular.VandiverUnitLemma
import Fermat.FiveHundredEightySeven.VandiverPolynomialUnits

/-!
# From Vandiver's deep congruence to the polynomial remainder at 587

This file formalizes the passage from Vandiver's local hypothesis

`u ≡ c^587 mod (1 - zeta)^1174`

and an exponent relation among the actual diagonal units to the integer
polynomial used in equations (3b)--(3d).

Integer exponents have already been cleared into a positive numerator `P`
and denominator `Q` in `VandiverPolynomialUnits`.  Here we prove:

* the deep congruence implies a congruence modulo `587^2`;
* the integer `c` is prime to `587`;
* the normalizations `6529^586` and `c^(587*586*t)` are `1` modulo `587^2`;
* the resulting algebraic correction is represented by an integer
  polynomial using the integral power basis; and
* the polynomial

  `A = P - C*Q - (587^2)*H`

  vanishes at `zeta` and satisfies `587^2 ∣ A(1)`.

The generic polynomial-remainder and high-derivative theorems can therefore
be applied without assuming any part of Vandiver's conclusion.
-/

open scoped BigOperators NumberField

namespace Fermat.FiveHundredEightySeven.VandiverDeepPolynomial

noncomputable section

open Polynomial
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.FiveHundredEightySeven.VandiverPolynomialUnits
open Fermat.FiveHundredEightySeven.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {587} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 587) K (by norm_num)

/-- One thousand one hundred seventy-four powers of the cyclotomic
uniformizer contain two powers
of the rational prime. -/
theorem fiveHundredEightySeven_sq_dvd_of_deep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587) (x : 𝓞 K)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 1174 ∣ x) :
    (587 : 𝓞 K) ^ 2 ∣ x := by
  have hbase : (hzeta.unit' : 𝓞 K) - 1 ∣
      (1 : 𝓞 K) - hzeta.unit' := by
    refine ⟨-1, ?_⟩
    ring
  have h1172 : ((hzeta.unit' : 𝓞 K) - 1) ^ 1172 ∣ x :=
    (pow_dvd_pow_of_dvd hbase 1172).trans
      ((pow_dvd_pow ((1 : 𝓞 K) - hzeta.unit') (by omega)).trans hdeep)
  have hp := (associated_zeta_sub_one_pow_prime hzeta).pow_pow (n := 2)
  have hExp1172 : (587 - 1 : ℕ) * 2 = 1172 := by norm_num
  have hCast587 : (((587 : ℕ) : 𝓞 K)) = (587 : 𝓞 K) := by norm_num
  have hp' : Associated (((hzeta.unit' : 𝓞 K) - 1) ^ 1172)
      ((587 : 𝓞 K) ^ 2) := by
    simpa only [← pow_mul, hExp1172, hCast587] using hp
  exact hp'.dvd_iff_dvd_left.mp h1172

/-- Raising a deeply congruent unit to Vandiver's outer exponent preserves
the congruence modulo `587^2`. -/
theorem deep_power_congruence587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 1174 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 587) :
    (587 : 𝓞 K) ^ 2 ∣
      (u : 𝓞 K) ^ (586 * t) -
        (c : 𝓞 K) ^ (587 * (586 * t)) := by
  have hbase : (587 : 𝓞 K) ^ 2 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 587 :=
    fiveHundredEightySeven_sq_dvd_of_deep hzeta _ hdeep
  have hpow := hbase.trans
    (sub_dvd_pow_sub_pow (u : 𝓞 K) ((c : 𝓞 K) ^ 587) (586 * t))
  convert hpow using 1
  rw [← pow_mul]

/-- The integer in a deep unit congruence cannot be divisible by `587`.
Otherwise the cyclotomic uniformizer would divide a unit. -/
theorem deep_integer_not_divisible587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587)
    (u : (𝓞 K)ˣ) (c : ℤ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 1174 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 587) :
    ¬(587 : ℤ) ∣ c := by
  intro hc
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  have h586 : (587 - 1 : ℕ) = 586 := by norm_num
  have hCast587 : (((587 : ℕ) : 𝓞 K)) = (587 : 𝓞 K) := by norm_num
  have hpipow : pi ^ 586 ∣ (587 : 𝓞 K) := by
    simpa only [pi, h586, hCast587] using
      (associated_zeta_sub_one_pow_prime hzeta).dvd
  have hpi587 : pi ∣ (587 : 𝓞 K) :=
    (dvd_pow_self pi (by norm_num : (586 : ℕ) ≠ 0)).trans hpipow
  obtain ⟨d, rfl⟩ := hc
  have hpic : pi ∣ (((587 : ℤ) * d : ℤ) : 𝓞 K) := by
    push_cast
    exact dvd_mul_of_dvd_left hpi587 _
  have hpicpow : pi ∣ ((((587 : ℤ) * d : ℤ) : 𝓞 K) ^ 587) :=
    hpic.trans (dvd_pow_self _ (by norm_num : (587 : ℕ) ≠ 0))
  have hpideep : pi ∣
      (u : 𝓞 K) - ((((587 : ℤ) * d : ℤ) : 𝓞 K) ^ 587) := by
    have hbase : pi ∣ (1 : 𝓞 K) - hzeta.unit' := by
      refine ⟨-1, ?_⟩
      dsimp [pi]
      ring
    exact hbase.trans
      ((dvd_pow_self ((1 : 𝓞 K) - hzeta.unit')
        (by norm_num : (1174 : ℕ) ≠ 0)).trans hdeep)
  have hpiu : pi ∣ (u : 𝓞 K) := by
    convert dvd_add hpideep hpicpow using 1
    ring
  exact hzeta.zeta_sub_one_prime'.not_unit
    (isUnit_of_dvd_unit hpiu u.isUnit)

/-! ## Evaluation at one modulo `587^2` -/

/-- The source's chosen Teichmüller representative satisfies
`6529^586 = 1 mod 587^2`. -/
theorem teichmuller6529_pow_fiveHundredEightySix :
    (6529 : ZMod (587 ^ 2)) ^ 586 = 1 := by
  simpa [Fermat.FiveHundredEightySeven.VandiverDiagonalArithmetic.teichmullerRoot587]
    using Fermat.FiveHundredEightySeven.VandiverDiagonalArithmetic.teichmullerRoot587_pow_card_sub_one

/-- Every basic Vandiver polynomial takes the value `6529` at `1`. -/
theorem eval_one_basicVandiverPolynomial587 (s : ℕ) :
    (basicVandiverPolynomial587 s).eval 1 = 6529 := by
  rw [basicVandiverPolynomial587, eval_mul, eval_pow, eval_X,
    eval_finsetSum]
  norm_num [Finset.sum_const]

/-- The value at one of every diagonal polynomial has 586th power one
modulo `587^2`. -/
theorem eval_one_diagonal_pow_fiveHundredEightySix
    (i : SourceIndex 587) :
    ((((diagonalVandiverPolynomial587 i).eval 1 : ℤ) :
      ZMod (587 ^ 2))) ^ 586 = 1 := by
  rw [diagonalVandiverPolynomial587, eval_prod]
  change ((Int.castRingHom (ZMod (587 ^ 2)))
      (∏ j, (basicVandiverPolynomial587 (conjugateExponent587 j) ^
        diagonalWeight587 i j).eval 1)) ^ 586 = 1
  rw [map_prod]
  rw [← Finset.prod_pow Finset.univ 586
    (fun j ↦ (Int.castRingHom (ZMod (587 ^ 2)))
      ((basicVandiverPolynomial587 (conjugateExponent587 j) ^
        diagonalWeight587 i j).eval 1))]
  apply Finset.prod_eq_one
  intro j hj
  rw [eval_pow, map_pow, eval_one_basicVandiverPolynomial587]
  calc
    (((6529 : ZMod (587 ^ 2)) ^ diagonalWeight587 i j) ^ 586) =
        ((6529 : ZMod (587 ^ 2)) ^ 586) ^ diagonalWeight587 i j := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega
    _ = 1 := by rw [teichmuller6529_pow_fiveHundredEightySix, one_pow]

/-- Every positive relation polynomial is `1` at one modulo `587^2`.
The outer exponent `586` is essential here. -/
theorem eval_one_positiveRelationPolynomial587_mod_sq
    (b : SourceIndex 587 → ℕ) :
    (((positiveRelationPolynomial587 b).eval 1 : ℤ) :
      ZMod (587 ^ 2)) = 1 := by
  rw [positiveRelationPolynomial587, eval_prod]
  change (Int.castRingHom (ZMod (587 ^ 2)))
      (∏ i, (diagonalVandiverPolynomial587 i ^ (586 * b i)).eval 1) = 1
  rw [map_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [eval_pow, map_pow]
  change ((((diagonalVandiverPolynomial587 i).eval 1 : ℤ) :
      ZMod (587 ^ 2)) ^ (586 * b i)) = 1
  rw [pow_mul, eval_one_diagonal_pow_fiveHundredEightySix, one_pow]

/-- Euler's theorem at modulus `587^2`, in precisely the exponent appearing
in the denominator-cleared unit relation. -/
theorem deep_integer_power_mod_sq
    (c : ℤ) (t : ℕ) (hc : ¬(587 : ℤ) ∣ c) :
    ((c ^ (587 * (586 * t)) : ℤ) : ZMod (587 ^ 2)) = 1 := by
  let m := c.natAbs
  have hmnot : ¬587 ∣ m := by
    intro hm
    apply hc
    rw [← Int.natAbs_dvd_natAbs]
    norm_num [m]
    exact hm
  have hcop587 : m.Coprime 587 :=
    ((show Nat.Prime 587 by norm_num).coprime_iff_not_dvd.mpr hmnot).symm
  have hcop : m.Coprime (587 ^ 2) := hcop587.pow_right 2
  have hmunit : IsUnit (m : ZMod (587 ^ 2)) :=
    (ZMod.isUnit_iff_coprime m (587 ^ 2)).mpr hcop
  have hcunit : IsUnit ((c : ℤ) : ZMod (587 ^ 2)) := by
    rcases Int.natAbs_eq c with h | h
    · rw [h]
      push_cast
      simpa [m] using hmunit
    · rw [h]
      push_cast
      simpa [m] using hmunit.neg
  let U : (ZMod (587 ^ 2))ˣ := hcunit.unit
  have hU : ((U : ZMod (587 ^ 2)) ^ (587 ^ 2).totient) = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg ((↑) : (ZMod (587 ^ 2))ˣ → ZMod (587 ^ 2))
        (ZMod.pow_totient U)
  have htotient : (587 ^ 2).totient = 587 * 586 := by
    simpa using Nat.totient_prime_pow (p := 587)
      (by norm_num) (n := 2) (by norm_num)
  have hbase : (((c : ℤ) : ZMod (587 ^ 2))) ^ (587 * 586) = 1 := by
    rw [hcunit.unit_spec] at hU
    simpa only [htotient] using hU
  push_cast
  rw [show 587 * (586 * t) = (587 * 586) * t by ring,
    pow_mul, hbase, one_pow]

/-! ## The vanishing polynomial -/

/-- The corrected relation polynomial.  Its third summand is the integral
power-basis representative of the algebraic `587^2` correction. -/
def vanishingRelationPolynomial587
    (P Q H : Polynomial ℤ) (C : ℤ) : Polynomial ℤ :=
  P - Polynomial.C C * Q - Polynomial.C (587 ^ 2 : ℤ) * H

/-- The exact source hinge preceding equation (3b): a deep unit relation
produces an integer polynomial which vanishes at `zeta` and whose value at
one is divisible by `587^2`. -/
theorem exists_vanishingRelationPolynomial587 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 587)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (a : SourceIndex 587 → ℤ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 1174 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 587)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit587 hzeta i ^ a i) :
    ∃ H : Polynomial ℤ,
      let P := positiveRelationPolynomial587 (fun i ↦ (a i).toNat)
      let Q := positiveRelationPolynomial587 (fun i ↦ (-a i).toNat)
      let C : ℤ := c ^ (587 * (586 * t))
      let A := vanishingRelationPolynomial587 P Q H C
      Polynomial.aeval zeta A = 0 ∧
        (587 : ℤ) ^ 2 ∣ A.eval 1 := by
  let P := positiveRelationPolynomial587 (fun i ↦ (a i).toNat)
  let Q := positiveRelationPolynomial587 (fun i ↦ (-a i).toNat)
  let C : ℤ := c ^ (587 * (586 * t))
  have hpow := deep_power_congruence587 hzeta u c t hdeep
  obtain ⟨beta, hbeta⟩ := hpow
  have heval :=
    eval₂_positive_relation_of_relation hzeta u t a hrel
  have hPQ :
      Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger P -
          (C : 𝓞 K) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q =
        (587 : 𝓞 K) ^ 2 *
          (beta * Polynomial.eval₂ (Int.castRingHom (𝓞 K))
            hzeta.toInteger Q) := by
    dsimp only [P, Q]
    rw [heval]
    dsimp only [C]
    push_cast
    calc
      (u : 𝓞 K) ^ (586 * t) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q -
          (c : 𝓞 K) ^ (587 * (586 * t)) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q =
        ((u : 𝓞 K) ^ (586 * t) -
          (c : 𝓞 K) ^ (587 * (586 * t))) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q := by
              ring
      _ = (587 : 𝓞 K) ^ 2 *
          (beta * Polynomial.eval₂ (Int.castRingHom (𝓞 K))
            hzeta.toInteger Q) := by rw [hbeta]; ring
  obtain ⟨H, hH⟩ := hzeta.integralPowerBasis.exists_eq_aeval'
    (beta * Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q)
  refine ⟨H, ?_, ?_⟩
  · have hH' :
        beta * Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q =
          Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger H := by
      have hcast :
          algebraMap ℤ (𝓞 K) = Int.castRingHom (𝓞 K) :=
        RingHom.eq_intCast' _
      simpa only [Polynomial.aeval_def,
        IsPrimitiveRoot.integralPowerBasis_gen, hcast] using hH
    have hzeroO : Polynomial.aeval hzeta.toInteger
        (vanishingRelationPolynomial587 P Q H C) = 0 := by
      rw [Polynomial.aeval_def]
      change Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (vanishingRelationPolynomial587 P Q H C) = 0
      rw [vanishingRelationPolynomial587, Polynomial.eval₂_sub,
        Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hH']
      have hcast587 : (Int.castRingHom (𝓞 K)) (587 ^ 2 : ℤ) =
          (587 : 𝓞 K) ^ 2 := by norm_num
      rw [hcast587]
      exact sub_eq_zero.mpr hPQ
    have hzeroK := congrArg ((↑) : 𝓞 K → K) hzeroO
    change Polynomial.aeval zeta
      (vanishingRelationPolynomial587 P Q H C) = 0
    simpa [Polynomial.aeval_def] using hzeroK
  · have hPmod :=
      eval_one_positiveRelationPolynomial587_mod_sq
        (fun i ↦ (a i).toNat)
    have hQmod :=
      eval_one_positiveRelationPolynomial587_mod_sq
        (fun i ↦ (-a i).toNat)
    have hcnot := deep_integer_not_divisible587 hzeta u c hdeep
    have hCmod := deep_integer_power_mod_sq c t hcnot
    have hAmod :
        (((vanishingRelationPolynomial587 P Q H C).eval 1 : ℤ) :
          ZMod (587 ^ 2)) = 0 := by
      rw [vanishingRelationPolynomial587, eval_sub, eval_sub,
        eval_mul, eval_mul, eval_C, eval_C]
      push_cast
      dsimp only [P, Q, C] at hPmod hQmod hCmod ⊢
      rw [hPmod, hQmod, hCmod]
      have hsqzero : (344569 : ZMod (587 ^ 2)) = 0 := by
        simpa using ZMod.natCast_self 344569
      rw [hsqzero]
      ring
    have hdvd :
        (((587 ^ 2 : ℕ) : ℤ) ∣
          (vanishingRelationPolynomial587 P Q H C).eval 1) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAmod
    norm_num at hdvd ⊢
    exact hdvd

end

end Fermat.FiveHundredEightySeven.VandiverDeepPolynomial
