import Fermat.Irregular.VandiverPolynomialRemainder
import Fermat.Irregular.VandiverUnitLemma
import Fermat.FourHundredNinetyOne.VandiverPolynomialUnits

/-!
# From Vandiver's deep congruence to the polynomial remainder at 491

This file formalizes the passage from Vandiver's local hypothesis

`u ≡ c^491 mod (1 - zeta)^982`

and an exponent relation among the actual diagonal units to the integer
polynomial used in equations (3b)--(3d).

Integer exponents have already been cleared into a positive numerator `P`
and denominator `Q` in `VandiverPolynomialUnits`.  Here we prove:

* the deep congruence implies a congruence modulo `491^2`;
* the integer `c` is prime to `491`;
* the normalizations `2512^490` and `c^(491*490*t)` are `1` modulo `491^2`;
* the algebraic correction is represented by an integer polynomial; and
* `A = P - C*Q - (491^2)*H` vanishes at `zeta` and has `491^2 ∣ A(1)`.
-/

open scoped BigOperators NumberField

namespace Fermat.FourHundredNinetyOne.VandiverDeepPolynomial

noncomputable section

open Polynomial
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.FourHundredNinetyOne.VandiverPolynomialUnits
open Fermat.FourHundredNinetyOne.VandiverDiagonalUnits

/- The prime fact must precede construction of the cyclotomic CM-field
instance; this declaration order avoids typeclass recursion. -/
local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {491} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 491) K (by norm_num)

/-- Nine hundred eighty-two powers of the cyclotomic uniformizer contain
two powers of the rational prime. -/
theorem fourHundredNinetyOne_sq_dvd_of_deep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491) (x : 𝓞 K)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 982 ∣ x) :
    (491 : 𝓞 K) ^ 2 ∣ x := by
  have hbase : (hzeta.unit' : 𝓞 K) - 1 ∣
      (1 : 𝓞 K) - hzeta.unit' := by
    refine ⟨-1, ?_⟩
    ring
  have h980 : ((hzeta.unit' : 𝓞 K) - 1) ^ 980 ∣ x :=
    (pow_dvd_pow_of_dvd hbase 980).trans
      ((pow_dvd_pow ((1 : 𝓞 K) - hzeta.unit') (by omega)).trans hdeep)
  have hp := (associated_zeta_sub_one_pow_prime hzeta).pow_pow (n := 2)
  have hExp980 : (491 - 1 : ℕ) * 2 = 980 := by norm_num
  have hCast491 : (((491 : ℕ) : 𝓞 K)) = (491 : 𝓞 K) := by norm_num
  have hp' : Associated (((hzeta.unit' : 𝓞 K) - 1) ^ 980)
      ((491 : 𝓞 K) ^ 2) := by
    simpa only [← pow_mul, hExp980, hCast491] using hp
  exact hp'.dvd_iff_dvd_left.mp h980

/-- Raising a deeply congruent unit to Vandiver's outer exponent preserves
the congruence modulo `491^2`. -/
theorem deep_power_congruence491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 982 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 491) :
    (491 : 𝓞 K) ^ 2 ∣
      (u : 𝓞 K) ^ (490 * t) -
        (c : 𝓞 K) ^ (491 * (490 * t)) := by
  have hbase : (491 : 𝓞 K) ^ 2 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 491 :=
    fourHundredNinetyOne_sq_dvd_of_deep hzeta _ hdeep
  have hpow := hbase.trans
    (sub_dvd_pow_sub_pow (u : 𝓞 K) ((c : 𝓞 K) ^ 491) (490 * t))
  convert hpow using 1
  rw [← pow_mul]

/-- The integer in a deep unit congruence cannot be divisible by `491`.
Otherwise the cyclotomic uniformizer would divide a unit. -/
theorem deep_integer_not_divisible491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491)
    (u : (𝓞 K)ˣ) (c : ℤ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 982 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 491) :
    ¬(491 : ℤ) ∣ c := by
  intro hc
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  have h490 : (491 - 1 : ℕ) = 490 := by norm_num
  have hCast491 : (((491 : ℕ) : 𝓞 K)) = (491 : 𝓞 K) := by norm_num
  have hpipow : pi ^ 490 ∣ (491 : 𝓞 K) := by
    simpa only [pi, h490, hCast491] using
      (associated_zeta_sub_one_pow_prime hzeta).dvd
  have hpi491 : pi ∣ (491 : 𝓞 K) :=
    (dvd_pow_self pi (by norm_num : (490 : ℕ) ≠ 0)).trans hpipow
  obtain ⟨d, rfl⟩ := hc
  have hpic : pi ∣ (((491 : ℤ) * d : ℤ) : 𝓞 K) := by
    push_cast
    exact dvd_mul_of_dvd_left hpi491 _
  have hpicpow : pi ∣ ((((491 : ℤ) * d : ℤ) : 𝓞 K) ^ 491) :=
    hpic.trans (dvd_pow_self _ (by norm_num : (491 : ℕ) ≠ 0))
  have hpideep : pi ∣
      (u : 𝓞 K) - ((((491 : ℤ) * d : ℤ) : 𝓞 K) ^ 491) := by
    have hbase : pi ∣ (1 : 𝓞 K) - hzeta.unit' := by
      refine ⟨-1, ?_⟩
      dsimp [pi]
      ring
    exact hbase.trans
      ((dvd_pow_self ((1 : 𝓞 K) - hzeta.unit')
        (by norm_num : (982 : ℕ) ≠ 0)).trans hdeep)
  have hpiu : pi ∣ (u : 𝓞 K) := by
    convert dvd_add hpideep hpicpow using 1
    ring
  exact hzeta.zeta_sub_one_prime'.not_unit
    (isUnit_of_dvd_unit hpiu u.isUnit)

/-! ## Evaluation at one modulo `491^2` -/

/-- The source's chosen Teichmüller representative satisfies
`2512^490 = 1 mod 491^2`. -/
theorem teichmuller2512_pow_fourHundredNinety :
    (2512 : ZMod (491 ^ 2)) ^ 490 = 1 := by
  simpa [Fermat.FourHundredNinetyOne.VandiverDiagonalArithmetic.teichmullerRoot491]
    using Fermat.FourHundredNinetyOne.VandiverDiagonalArithmetic.teichmullerRoot491_pow_card_sub_one

/-- Every basic Vandiver polynomial takes the value `2512` at `1`. -/
theorem eval_one_basicVandiverPolynomial491 (s : ℕ) :
    (basicVandiverPolynomial491 s).eval 1 = 2512 := by
  rw [basicVandiverPolynomial491, eval_mul, eval_pow, eval_X,
    eval_finsetSum]
  norm_num [Finset.sum_const]

/-- The value at one of every diagonal polynomial has 490th power one
modulo `491^2`. -/
theorem eval_one_diagonal_pow_fourHundredNinety
    (i : SourceIndex 491) :
    ((((diagonalVandiverPolynomial491 i).eval 1 : ℤ) :
      ZMod (491 ^ 2))) ^ 490 = 1 := by
  rw [diagonalVandiverPolynomial491, eval_prod]
  change ((Int.castRingHom (ZMod (491 ^ 2)))
      (∏ j, (basicVandiverPolynomial491 (conjugateExponent491 j) ^
        diagonalWeight491 i j).eval 1)) ^ 490 = 1
  rw [map_prod]
  rw [← Finset.prod_pow Finset.univ 490
    (fun j ↦ (Int.castRingHom (ZMod (491 ^ 2)))
      ((basicVandiverPolynomial491 (conjugateExponent491 j) ^
        diagonalWeight491 i j).eval 1))]
  apply Finset.prod_eq_one
  intro j hj
  rw [eval_pow, map_pow, eval_one_basicVandiverPolynomial491]
  calc
    (((2512 : ZMod (491 ^ 2)) ^ diagonalWeight491 i j) ^ 490) =
        ((2512 : ZMod (491 ^ 2)) ^ 490) ^ diagonalWeight491 i j := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega
    _ = 1 := by rw [teichmuller2512_pow_fourHundredNinety, one_pow]

/-- Every positive relation polynomial is `1` at one modulo `491^2`.
The outer exponent `490` is essential here. -/
theorem eval_one_positiveRelationPolynomial491_mod_sq
    (b : SourceIndex 491 → ℕ) :
    (((positiveRelationPolynomial491 b).eval 1 : ℤ) :
      ZMod (491 ^ 2)) = 1 := by
  rw [positiveRelationPolynomial491, eval_prod]
  change (Int.castRingHom (ZMod (491 ^ 2)))
      (∏ i, (diagonalVandiverPolynomial491 i ^ (490 * b i)).eval 1) = 1
  rw [map_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [eval_pow, map_pow]
  change ((((diagonalVandiverPolynomial491 i).eval 1 : ℤ) :
      ZMod (491 ^ 2)) ^ (490 * b i)) = 1
  rw [pow_mul, eval_one_diagonal_pow_fourHundredNinety, one_pow]

/-- Euler's theorem at modulus `491^2`, in precisely the exponent appearing
in the denominator-cleared unit relation. -/
theorem deep_integer_power_mod_sq
    (c : ℤ) (t : ℕ) (hc : ¬(491 : ℤ) ∣ c) :
    ((c ^ (491 * (490 * t)) : ℤ) : ZMod (491 ^ 2)) = 1 := by
  let m := c.natAbs
  have hmnot : ¬491 ∣ m := by
    intro hm
    apply hc
    rw [← Int.natAbs_dvd_natAbs]
    norm_num [m]
    exact hm
  have hcop491 : m.Coprime 491 :=
    ((show Nat.Prime 491 by norm_num).coprime_iff_not_dvd.mpr hmnot).symm
  have hcop : m.Coprime (491 ^ 2) := hcop491.pow_right 2
  have hmunit : IsUnit (m : ZMod (491 ^ 2)) :=
    (ZMod.isUnit_iff_coprime m (491 ^ 2)).mpr hcop
  have hcunit : IsUnit ((c : ℤ) : ZMod (491 ^ 2)) := by
    rcases Int.natAbs_eq c with h | h
    · rw [h]
      push_cast
      simpa [m] using hmunit
    · rw [h]
      push_cast
      simpa [m] using hmunit.neg
  let U : (ZMod (491 ^ 2))ˣ := hcunit.unit
  have hU : ((U : ZMod (491 ^ 2)) ^ (491 ^ 2).totient) = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg ((↑) : (ZMod (491 ^ 2))ˣ → ZMod (491 ^ 2))
        (ZMod.pow_totient U)
  have htotient : (491 ^ 2).totient = 491 * 490 := by
    simpa using Nat.totient_prime_pow (p := 491)
      (by norm_num) (n := 2) (by norm_num)
  have hbase : (((c : ℤ) : ZMod (491 ^ 2))) ^ (491 * 490) = 1 := by
    rw [hcunit.unit_spec] at hU
    simpa only [htotient] using hU
  push_cast
  rw [show 491 * (490 * t) = (491 * 490) * t by ring,
    pow_mul, hbase, one_pow]

/-! ## The vanishing polynomial -/

/-- The corrected relation polynomial.  Its third summand is the integral
power-basis representative of the algebraic `491^2` correction. -/
def vanishingRelationPolynomial491
    (P Q H : Polynomial ℤ) (C : ℤ) : Polynomial ℤ :=
  P - Polynomial.C C * Q - Polynomial.C (491 ^ 2 : ℤ) * H

/-- A deep unit relation produces an integer polynomial which vanishes at
`zeta` and whose value at one is divisible by `491^2`. -/
theorem exists_vanishingRelationPolynomial491 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 491)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (a : SourceIndex 491 → ℤ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 982 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 491)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit491 hzeta i ^ a i) :
    ∃ H : Polynomial ℤ,
      let P := positiveRelationPolynomial491 (fun i ↦ (a i).toNat)
      let Q := positiveRelationPolynomial491 (fun i ↦ (-a i).toNat)
      let C : ℤ := c ^ (491 * (490 * t))
      let A := vanishingRelationPolynomial491 P Q H C
      Polynomial.aeval zeta A = 0 ∧
        (491 : ℤ) ^ 2 ∣ A.eval 1 := by
  let P := positiveRelationPolynomial491 (fun i ↦ (a i).toNat)
  let Q := positiveRelationPolynomial491 (fun i ↦ (-a i).toNat)
  let C : ℤ := c ^ (491 * (490 * t))
  have hpow := deep_power_congruence491 hzeta u c t hdeep
  obtain ⟨beta, hbeta⟩ := hpow
  have heval :=
    eval₂_positive_relation_of_relation hzeta u t a hrel
  have hPQ :
      Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger P -
          (C : 𝓞 K) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q =
        (491 : 𝓞 K) ^ 2 *
          (beta * Polynomial.eval₂ (Int.castRingHom (𝓞 K))
            hzeta.toInteger Q) := by
    dsimp only [P, Q]
    rw [heval]
    dsimp only [C]
    push_cast
    calc
      (u : 𝓞 K) ^ (490 * t) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q -
          (c : 𝓞 K) ^ (491 * (490 * t)) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q =
        ((u : 𝓞 K) ^ (490 * t) -
          (c : 𝓞 K) ^ (491 * (490 * t))) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q := by
              ring
      _ = (491 : 𝓞 K) ^ 2 *
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
        (vanishingRelationPolynomial491 P Q H C) = 0 := by
      rw [Polynomial.aeval_def]
      change Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (vanishingRelationPolynomial491 P Q H C) = 0
      rw [vanishingRelationPolynomial491, Polynomial.eval₂_sub,
        Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hH']
      have hcast491 : (Int.castRingHom (𝓞 K)) (491 ^ 2 : ℤ) =
          (491 : 𝓞 K) ^ 2 := by norm_num
      rw [hcast491]
      exact sub_eq_zero.mpr hPQ
    have hzeroK := congrArg ((↑) : 𝓞 K → K) hzeroO
    change Polynomial.aeval zeta
      (vanishingRelationPolynomial491 P Q H C) = 0
    simpa [Polynomial.aeval_def] using hzeroK
  · have hPmod :=
      eval_one_positiveRelationPolynomial491_mod_sq
        (fun i ↦ (a i).toNat)
    have hQmod :=
      eval_one_positiveRelationPolynomial491_mod_sq
        (fun i ↦ (-a i).toNat)
    have hcnot := deep_integer_not_divisible491 hzeta u c hdeep
    have hCmod := deep_integer_power_mod_sq c t hcnot
    have hAmod :
        (((vanishingRelationPolynomial491 P Q H C).eval 1 : ℤ) :
          ZMod (491 ^ 2)) = 0 := by
      rw [vanishingRelationPolynomial491, eval_sub, eval_sub,
        eval_mul, eval_mul, eval_C, eval_C]
      push_cast
      dsimp only [P, Q, C] at hPmod hQmod hCmod ⊢
      rw [hPmod, hQmod, hCmod]
      have hsqzero : (241081 : ZMod (491 ^ 2)) = 0 := by
        simpa using ZMod.natCast_self 241081
      rw [hsqzero]
      ring
    have hdvd :
        (((491 ^ 2 : ℕ) : ℤ) ∣
          (vanishingRelationPolynomial491 P Q H C).eval 1) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAmod
    norm_num at hdvd ⊢
    exact hdvd

end

end Fermat.FourHundredNinetyOne.VandiverDeepPolynomial
