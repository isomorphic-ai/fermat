import Fermat.Irregular.VandiverPolynomialRemainder
import Fermat.Irregular.VandiverUnitLemma
import Fermat.ThirtySeven.VandiverPolynomialUnits

/-!
# From Vandiver's deep congruence to the polynomial remainder at 37

This file formalizes the passage from Vandiver's local hypothesis

`u ≡ c^37 mod (1 - zeta)^74`

and an exponent relation among the actual diagonal units to the integer
polynomial used in equations (3b)--(3d).

Integer exponents have already been cleared into a positive numerator `P`
and denominator `Q` in `VandiverPolynomialUnits`.  Here we prove:

* the deep congruence implies a congruence modulo `37^2`;
* the integer `c` is prime to `37`;
* the normalizations `76^36` and `c^(37*36*t)` are `1` modulo `37^2`;
* the resulting algebraic correction is represented by an integer
  polynomial using the integral power basis; and
* the polynomial

  `A = P - C*Cpoly*Q - C*(37^2)*H`

  vanishes at `zeta` and satisfies `37^2 ∣ A(1)`.

The generic polynomial-remainder and high-derivative theorems can therefore
be applied without assuming any part of Vandiver's conclusion.
-/

open scoped BigOperators NumberField

namespace Fermat.ThirtySeven.VandiverDeepPolynomial

noncomputable section

open Polynomial
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.ThirtySeven.VandiverPolynomialUnits
open Fermat.ThirtySeven.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 37) K (by norm_num)

/-- Seventy-four powers of the cyclotomic uniformizer contain two powers
of the rational prime. -/
theorem thirtySeven_sq_dvd_of_deep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37) (x : 𝓞 K)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 74 ∣ x) :
    (37 : 𝓞 K) ^ 2 ∣ x := by
  have hbase : (hzeta.unit' : 𝓞 K) - 1 ∣
      (1 : 𝓞 K) - hzeta.unit' := by
    refine ⟨-1, ?_⟩
    ring
  have h72 : ((hzeta.unit' : 𝓞 K) - 1) ^ 72 ∣ x :=
    (pow_dvd_pow_of_dvd hbase 72).trans
      ((pow_dvd_pow ((1 : 𝓞 K) - hzeta.unit') (by omega)).trans hdeep)
  have hp := (associated_zeta_sub_one_pow_prime hzeta).pow_pow (n := 2)
  have hExp72 : (37 - 1 : ℕ) * 2 = 72 := by norm_num
  have hCast37 : (((37 : ℕ) : 𝓞 K)) = (37 : 𝓞 K) := by norm_num
  have hp' : Associated (((hzeta.unit' : 𝓞 K) - 1) ^ 72)
      ((37 : 𝓞 K) ^ 2) := by
    simpa only [← pow_mul, hExp72, hCast37] using hp
  exact hp'.dvd_iff_dvd_left.mp h72

/-- Raising a deeply congruent unit to Vandiver's outer exponent preserves
the congruence modulo `37^2`. -/
theorem deep_power_congruence37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 74 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 37) :
    (37 : 𝓞 K) ^ 2 ∣
      (u : 𝓞 K) ^ (36 * t) -
        (c : 𝓞 K) ^ (37 * (36 * t)) := by
  have hbase : (37 : 𝓞 K) ^ 2 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 37 :=
    thirtySeven_sq_dvd_of_deep hzeta _ hdeep
  have hpow := hbase.trans
    (sub_dvd_pow_sub_pow (u : 𝓞 K) ((c : 𝓞 K) ^ 37) (36 * t))
  convert hpow using 1
  rw [← pow_mul]

/-- The integer in a deep unit congruence cannot be divisible by `37`.
Otherwise the cyclotomic uniformizer would divide a unit. -/
theorem deep_integer_not_divisible37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37)
    (u : (𝓞 K)ˣ) (c : ℤ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 74 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 37) :
    ¬(37 : ℤ) ∣ c := by
  intro hc
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  have h36 : (37 - 1 : ℕ) = 36 := by norm_num
  have hCast37 : (((37 : ℕ) : 𝓞 K)) = (37 : 𝓞 K) := by norm_num
  have hpipow : pi ^ 36 ∣ (37 : 𝓞 K) := by
    simpa only [pi, h36, hCast37] using
      (associated_zeta_sub_one_pow_prime hzeta).dvd
  have hpi37 : pi ∣ (37 : 𝓞 K) :=
    (dvd_pow_self pi (by norm_num : (36 : ℕ) ≠ 0)).trans hpipow
  obtain ⟨d, rfl⟩ := hc
  have hpic : pi ∣ (((37 : ℤ) * d : ℤ) : 𝓞 K) := by
    push_cast
    exact dvd_mul_of_dvd_left hpi37 _
  have hpicpow : pi ∣ ((((37 : ℤ) * d : ℤ) : 𝓞 K) ^ 37) :=
    hpic.trans (dvd_pow_self _ (by norm_num : (37 : ℕ) ≠ 0))
  have hpideep : pi ∣
      (u : 𝓞 K) - ((((37 : ℤ) * d : ℤ) : 𝓞 K) ^ 37) := by
    have hbase : pi ∣ (1 : 𝓞 K) - hzeta.unit' := by
      refine ⟨-1, ?_⟩
      dsimp [pi]
      ring
    exact hbase.trans
      ((dvd_pow_self ((1 : 𝓞 K) - hzeta.unit')
        (by norm_num : (74 : ℕ) ≠ 0)).trans hdeep)
  have hpiu : pi ∣ (u : 𝓞 K) := by
    convert dvd_add hpideep hpicpow using 1
    ring
  exact hzeta.zeta_sub_one_prime'.not_unit
    (isUnit_of_dvd_unit hpiu u.isUnit)

/-! ## Evaluation at one modulo `37^2` -/

/-- The source's chosen Teichmüller representative satisfies
`76^36 = 1 mod 37^2`. -/
theorem teichmuller76_pow_thirtySix :
    (76 : ZMod (37 ^ 2)) ^ 36 = 1 := by
  have hdvd : (1369 : ℤ) ∣ (76 : ℤ) ^ 36 - 1 := by norm_num
  have hz : ((((76 : ℤ) ^ 36 - 1 : ℤ)) : ZMod (37 ^ 2)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa using hdvd)
  push_cast at hz
  exact sub_eq_zero.mp hz

/-- Every basic Vandiver polynomial takes the value `76` at `1`. -/
theorem eval_one_basicVandiverPolynomial37 (s : ℕ) :
    (basicVandiverPolynomial37 s).eval 1 = 76 := by
  rw [basicVandiverPolynomial37, eval_mul, eval_pow, eval_X,
    eval_finsetSum]
  norm_num [Finset.sum_const]

/-- The value at one of every diagonal polynomial has 36th power one
modulo `37^2`. -/
theorem eval_one_diagonal_pow_thirtySix
    (i : SourceIndex 37) :
    ((((diagonalVandiverPolynomial37 i).eval 1 : ℤ) :
      ZMod (37 ^ 2))) ^ 36 = 1 := by
  rw [diagonalVandiverPolynomial37, eval_prod]
  change ((Int.castRingHom (ZMod (37 ^ 2)))
      (∏ j, (basicVandiverPolynomial37 (conjugateExponent37 j) ^
        diagonalWeight37 i j).eval 1)) ^ 36 = 1
  rw [map_prod]
  rw [← Finset.prod_pow Finset.univ 36
    (fun j ↦ (Int.castRingHom (ZMod (37 ^ 2)))
      ((basicVandiverPolynomial37 (conjugateExponent37 j) ^
        diagonalWeight37 i j).eval 1))]
  apply Finset.prod_eq_one
  intro j hj
  rw [eval_pow, map_pow, eval_one_basicVandiverPolynomial37]
  calc
    (((76 : ZMod (37 ^ 2)) ^ diagonalWeight37 i j) ^ 36) =
        ((76 : ZMod (37 ^ 2)) ^ 36) ^ diagonalWeight37 i j := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega
    _ = 1 := by rw [teichmuller76_pow_thirtySix, one_pow]

/-- Every positive relation polynomial is `1` at one modulo `37^2`.
The outer exponent `36` is essential here. -/
theorem eval_one_positiveRelationPolynomial37_mod_sq
    (b : SourceIndex 37 → ℕ) :
    (((positiveRelationPolynomial37 b).eval 1 : ℤ) :
      ZMod (37 ^ 2)) = 1 := by
  rw [positiveRelationPolynomial37, eval_prod]
  change (Int.castRingHom (ZMod (37 ^ 2)))
      (∏ i, (diagonalVandiverPolynomial37 i ^ (36 * b i)).eval 1) = 1
  rw [map_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [eval_pow, map_pow]
  change ((((diagonalVandiverPolynomial37 i).eval 1 : ℤ) :
      ZMod (37 ^ 2)) ^ (36 * b i)) = 1
  rw [pow_mul, eval_one_diagonal_pow_thirtySix, one_pow]

/-- Euler's theorem at modulus `37^2`, in precisely the exponent appearing
in the denominator-cleared unit relation. -/
theorem deep_integer_power_mod_sq
    (c : ℤ) (t : ℕ) (hc : ¬(37 : ℤ) ∣ c) :
    ((c ^ (37 * (36 * t)) : ℤ) : ZMod (37 ^ 2)) = 1 := by
  let m := c.natAbs
  have hmnot : ¬37 ∣ m := by
    intro hm
    apply hc
    rw [← Int.natAbs_dvd_natAbs]
    norm_num [m]
    exact hm
  have hcop37 : m.Coprime 37 :=
    ((show Nat.Prime 37 by norm_num).coprime_iff_not_dvd.mpr hmnot).symm
  have hcop : m.Coprime (37 ^ 2) := hcop37.pow_right 2
  have hmunit : IsUnit (m : ZMod (37 ^ 2)) :=
    (ZMod.isUnit_iff_coprime m (37 ^ 2)).mpr hcop
  have hcunit : IsUnit ((c : ℤ) : ZMod (37 ^ 2)) := by
    rcases Int.natAbs_eq c with h | h
    · rw [h]
      push_cast
      simpa [m] using hmunit
    · rw [h]
      push_cast
      simpa [m] using hmunit.neg
  let U : (ZMod (37 ^ 2))ˣ := hcunit.unit
  have hU : ((U : ZMod (37 ^ 2)) ^ (37 ^ 2).totient) = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg ((↑) : (ZMod (37 ^ 2))ˣ → ZMod (37 ^ 2))
        (ZMod.pow_totient U)
  have htotient : (37 ^ 2).totient = 37 * 36 := by
    simpa using Nat.totient_prime_pow (p := 37)
      (by norm_num) (n := 2) (by norm_num)
  have hbase : (((c : ℤ) : ZMod (37 ^ 2))) ^ (37 * 36) = 1 := by
    rw [hcunit.unit_spec] at hU
    simpa only [htotient] using hU
  push_cast
  rw [show 37 * (36 * t) = (37 * 36) * t by ring,
    pow_mul, hbase, one_pow]

/-! ## The vanishing polynomial -/

/-- The corrected relation polynomial.  Its third summand is the integral
power-basis representative of the algebraic `37^2` correction. -/
def vanishingRelationPolynomial37
    (P Q H : Polynomial ℤ) (C : ℤ) : Polynomial ℤ :=
  P - Polynomial.C C * Q - Polynomial.C (37 ^ 2 : ℤ) * H

/-- The exact source hinge preceding equation (3b): a deep unit relation
produces an integer polynomial which vanishes at `zeta` and whose value at
one is divisible by `37^2`. -/
theorem exists_vanishingRelationPolynomial37 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 37)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (a : SourceIndex 37 → ℤ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 74 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 37)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit37 hzeta i ^ a i) :
    ∃ H : Polynomial ℤ,
      let P := positiveRelationPolynomial37 (fun i ↦ (a i).toNat)
      let Q := positiveRelationPolynomial37 (fun i ↦ (-a i).toNat)
      let C : ℤ := c ^ (37 * (36 * t))
      let A := vanishingRelationPolynomial37 P Q H C
      Polynomial.aeval zeta A = 0 ∧
        (37 : ℤ) ^ 2 ∣ A.eval 1 := by
  let P := positiveRelationPolynomial37 (fun i ↦ (a i).toNat)
  let Q := positiveRelationPolynomial37 (fun i ↦ (-a i).toNat)
  let C : ℤ := c ^ (37 * (36 * t))
  have hpow := deep_power_congruence37 hzeta u c t hdeep
  obtain ⟨beta, hbeta⟩ := hpow
  have heval :=
    eval₂_positive_relation_of_relation hzeta u t a hrel
  have hPQ :
      Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger P -
          (C : 𝓞 K) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q =
        (37 : 𝓞 K) ^ 2 *
          (beta * Polynomial.eval₂ (Int.castRingHom (𝓞 K))
            hzeta.toInteger Q) := by
    dsimp only [P, Q]
    rw [heval]
    dsimp only [C]
    push_cast
    calc
      (u : 𝓞 K) ^ (36 * t) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q -
          (c : 𝓞 K) ^ (37 * (36 * t)) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q =
        ((u : 𝓞 K) ^ (36 * t) -
          (c : 𝓞 K) ^ (37 * (36 * t))) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q := by
              ring
      _ = (37 : 𝓞 K) ^ 2 *
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
        (vanishingRelationPolynomial37 P Q H C) = 0 := by
      rw [Polynomial.aeval_def]
      change Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (vanishingRelationPolynomial37 P Q H C) = 0
      rw [vanishingRelationPolynomial37, Polynomial.eval₂_sub,
        Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hH']
      have hcast37 : (Int.castRingHom (𝓞 K)) (37 ^ 2 : ℤ) =
          (37 : 𝓞 K) ^ 2 := by norm_num
      rw [hcast37]
      exact sub_eq_zero.mpr hPQ
    have hzeroK := congrArg ((↑) : 𝓞 K → K) hzeroO
    change Polynomial.aeval zeta
      (vanishingRelationPolynomial37 P Q H C) = 0
    simpa [Polynomial.aeval_def] using hzeroK
  · have hPmod :=
      eval_one_positiveRelationPolynomial37_mod_sq
        (fun i ↦ (a i).toNat)
    have hQmod :=
      eval_one_positiveRelationPolynomial37_mod_sq
        (fun i ↦ (-a i).toNat)
    have hcnot := deep_integer_not_divisible37 hzeta u c hdeep
    have hCmod := deep_integer_power_mod_sq c t hcnot
    have hAmod :
        (((vanishingRelationPolynomial37 P Q H C).eval 1 : ℤ) :
          ZMod (37 ^ 2)) = 0 := by
      rw [vanishingRelationPolynomial37, eval_sub, eval_sub,
        eval_mul, eval_mul, eval_C, eval_C]
      push_cast
      dsimp only [P, Q, C] at hPmod hQmod hCmod ⊢
      rw [hPmod, hQmod, hCmod]
      have hsqzero : (1369 : ZMod (37 ^ 2)) = 0 := by
        simpa using ZMod.natCast_self 1369
      rw [hsqzero]
      ring
    have hdvd :
        (((37 ^ 2 : ℕ) : ℤ) ∣
          (vanishingRelationPolynomial37 P Q H C).eval 1) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAmod
    norm_num at hdvd ⊢
    exact hdvd

end

end Fermat.ThirtySeven.VandiverDeepPolynomial
