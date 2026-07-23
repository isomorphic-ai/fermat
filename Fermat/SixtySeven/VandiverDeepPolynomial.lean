import Fermat.Irregular.VandiverPolynomialRemainder
import Fermat.Irregular.VandiverUnitLemma
import Fermat.SixtySeven.VandiverPolynomialUnits

/-!
# From Vandiver's deep congruence to the polynomial remainder at 67

This file formalizes the passage from Vandiver's local hypothesis

`u ≡ c^67 mod (1 - zeta)^134`

and an exponent relation among the actual diagonal units to the integer
polynomial used in equations (3b)--(3d).

Integer exponents have already been cleared into a positive numerator `P`
and denominator `Q` in `VandiverPolynomialUnits`.  Here we prove:

* the deep congruence implies a congruence modulo `67^2`;
* the integer `c` is prime to `67`;
* the normalizations `1342^66` and `c^(67*66*t)` are `1` modulo `67^2`;
* the resulting algebraic correction is represented by an integer
  polynomial using the integral power basis; and
* the polynomial

  `A = P - C*Cpoly*Q - C*(67^2)*H`

  vanishes at `zeta` and satisfies `67^2 ∣ A(1)`.

The generic polynomial-remainder and high-derivative theorems can therefore
be applied without assuming any part of Vandiver's conclusion.
-/

open scoped BigOperators NumberField

namespace Fermat.SixtySeven.VandiverDeepPolynomial

noncomputable section

open Polynomial
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.SixtySeven.VandiverPolynomialUnits
open Fermat.SixtySeven.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {67} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 67) K (by norm_num)

/-- One hundred thirty-four powers of the cyclotomic uniformizer contain two powers
of the rational prime. -/
theorem sixtySeven_sq_dvd_of_deep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67) (x : 𝓞 K)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 134 ∣ x) :
    (67 : 𝓞 K) ^ 2 ∣ x := by
  have hbase : (hzeta.unit' : 𝓞 K) - 1 ∣
      (1 : 𝓞 K) - hzeta.unit' := by
    refine ⟨-1, ?_⟩
    ring
  have h132 : ((hzeta.unit' : 𝓞 K) - 1) ^ 132 ∣ x :=
    (pow_dvd_pow_of_dvd hbase 132).trans
      ((pow_dvd_pow ((1 : 𝓞 K) - hzeta.unit') (by omega)).trans hdeep)
  have hp := (associated_zeta_sub_one_pow_prime hzeta).pow_pow (n := 2)
  have hp' : Associated (((hzeta.unit' : 𝓞 K) - 1) ^ 132)
      ((67 : 𝓞 K) ^ 2) := by
    simpa only [← pow_mul] using hp
  exact hp'.dvd_iff_dvd_left.mp h132

/-- Raising a deeply congruent unit to Vandiver's outer exponent preserves
the congruence modulo `67^2`. -/
theorem deep_power_congruence67 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 134 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 67) :
    (67 : 𝓞 K) ^ 2 ∣
      (u : 𝓞 K) ^ (66 * t) -
        (c : 𝓞 K) ^ (67 * (66 * t)) := by
  have hbase : (67 : 𝓞 K) ^ 2 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 67 :=
    sixtySeven_sq_dvd_of_deep hzeta _ hdeep
  have hpow := hbase.trans
    (sub_dvd_pow_sub_pow (u : 𝓞 K) ((c : 𝓞 K) ^ 67) (66 * t))
  convert hpow using 1
  rw [← pow_mul]

/-- The integer in a deep unit congruence cannot be divisible by `67`.
Otherwise the cyclotomic uniformizer would divide a unit. -/
theorem deep_integer_not_divisible67 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67)
    (u : (𝓞 K)ˣ) (c : ℤ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 134 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 67) :
    ¬(67 : ℤ) ∣ c := by
  intro hc
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  have hpipow : pi ^ 66 ∣ (67 : 𝓞 K) := by
    simpa only [pi] using (associated_zeta_sub_one_pow_prime hzeta).dvd
  have hpi67 : pi ∣ (67 : 𝓞 K) :=
    (dvd_pow_self pi (by norm_num : (66 : ℕ) ≠ 0)).trans hpipow
  obtain ⟨d, rfl⟩ := hc
  have hpic : pi ∣ (((67 : ℤ) * d : ℤ) : 𝓞 K) := by
    push_cast
    exact dvd_mul_of_dvd_left hpi67 _
  have hpicpow : pi ∣ ((((67 : ℤ) * d : ℤ) : 𝓞 K) ^ 67) :=
    hpic.trans (dvd_pow_self _ (by norm_num : (67 : ℕ) ≠ 0))
  have hpideep : pi ∣
      (u : 𝓞 K) - ((((67 : ℤ) * d : ℤ) : 𝓞 K) ^ 67) := by
    have hbase : pi ∣ (1 : 𝓞 K) - hzeta.unit' := by
      refine ⟨-1, ?_⟩
      dsimp [pi]
      ring
    exact hbase.trans
      ((dvd_pow_self ((1 : 𝓞 K) - hzeta.unit')
        (by norm_num : (134 : ℕ) ≠ 0)).trans hdeep)
  have hpiu : pi ∣ (u : 𝓞 K) := by
    convert dvd_add hpideep hpicpow using 1
    ring
  exact hzeta.zeta_sub_one_prime'.not_unit
    (isUnit_of_dvd_unit hpiu u.isUnit)

/-! ## Evaluation at one modulo `67^2` -/

/-- The source's chosen Teichmüller representative satisfies
`1342^66 = 1 mod 67^2`. -/
theorem teichmuller1342_pow_sixtySix :
    (1342 : ZMod (67 ^ 2)) ^ 66 = 1 := by
  have hdvd : (4489 : ℤ) ∣ (1342 : ℤ) ^ 66 - 1 := by norm_num
  have hz : ((((1342 : ℤ) ^ 66 - 1 : ℤ)) : ZMod (67 ^ 2)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa using hdvd)
  push_cast at hz
  exact sub_eq_zero.mp hz

/-- Every basic Vandiver polynomial takes the value `1342` at `1`. -/
theorem eval_one_basicVandiverPolynomial67 (s : ℕ) :
    (basicVandiverPolynomial67 s).eval 1 = 1342 := by
  rw [basicVandiverPolynomial67, eval_mul, eval_pow, eval_X,
    eval_finsetSum]
  norm_num [Finset.sum_const]

/-- The value at one of every diagonal polynomial has 66th power one
modulo `67^2`. -/
theorem eval_one_diagonal_pow_sixtySix
    (i : SourceIndex 67) :
    ((((diagonalVandiverPolynomial67 i).eval 1 : ℤ) :
      ZMod (67 ^ 2))) ^ 66 = 1 := by
  rw [diagonalVandiverPolynomial67, eval_prod]
  change ((Int.castRingHom (ZMod (67 ^ 2)))
      (∏ j, (basicVandiverPolynomial67 (conjugateExponent67 j) ^
        diagonalWeight67 i j).eval 1)) ^ 66 = 1
  rw [map_prod]
  rw [← Finset.prod_pow Finset.univ 66
    (fun j ↦ (Int.castRingHom (ZMod (67 ^ 2)))
      ((basicVandiverPolynomial67 (conjugateExponent67 j) ^
        diagonalWeight67 i j).eval 1))]
  apply Finset.prod_eq_one
  intro j hj
  rw [eval_pow, map_pow, eval_one_basicVandiverPolynomial67]
  calc
    (((1342 : ZMod (67 ^ 2)) ^ diagonalWeight67 i j) ^ 66) =
        ((1342 : ZMod (67 ^ 2)) ^ 66) ^ diagonalWeight67 i j := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega
    _ = 1 := by rw [teichmuller1342_pow_sixtySix, one_pow]

/-- Every positive relation polynomial is `1` at one modulo `67^2`.
The outer exponent `66` is essential here. -/
theorem eval_one_positiveRelationPolynomial67_mod_sq
    (b : SourceIndex 67 → ℕ) :
    (((positiveRelationPolynomial67 b).eval 1 : ℤ) :
      ZMod (67 ^ 2)) = 1 := by
  rw [positiveRelationPolynomial67, eval_prod]
  change (Int.castRingHom (ZMod (67 ^ 2)))
      (∏ i, (diagonalVandiverPolynomial67 i ^ (66 * b i)).eval 1) = 1
  rw [map_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [eval_pow, map_pow]
  change ((((diagonalVandiverPolynomial67 i).eval 1 : ℤ) :
      ZMod (67 ^ 2)) ^ (66 * b i)) = 1
  rw [pow_mul, eval_one_diagonal_pow_sixtySix, one_pow]

/-- Euler's theorem at modulus `67^2`, in precisely the exponent appearing
in the denominator-cleared unit relation. -/
theorem deep_integer_power_mod_sq
    (c : ℤ) (t : ℕ) (hc : ¬(67 : ℤ) ∣ c) :
    ((c ^ (67 * (66 * t)) : ℤ) : ZMod (67 ^ 2)) = 1 := by
  let m := c.natAbs
  have hmnot : ¬67 ∣ m := by
    intro hm
    apply hc
    rw [← Int.natAbs_dvd_natAbs]
    norm_num [m]
    exact hm
  have hcop67 : m.Coprime 67 :=
    ((show Nat.Prime 67 by norm_num).coprime_iff_not_dvd.mpr hmnot).symm
  have hcop : m.Coprime (67 ^ 2) := hcop67.pow_right 2
  have hmunit : IsUnit (m : ZMod (67 ^ 2)) :=
    (ZMod.isUnit_iff_coprime m (67 ^ 2)).mpr hcop
  have hcunit : IsUnit ((c : ℤ) : ZMod (67 ^ 2)) := by
    rcases Int.natAbs_eq c with h | h
    · rw [h]
      push_cast
      simpa [m] using hmunit
    · rw [h]
      push_cast
      simpa [m] using hmunit.neg
  let U : (ZMod (67 ^ 2))ˣ := hcunit.unit
  have hU : ((U : ZMod (67 ^ 2)) ^ (67 ^ 2).totient) = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg ((↑) : (ZMod (67 ^ 2))ˣ → ZMod (67 ^ 2))
        (ZMod.pow_totient U)
  have htotient : (67 ^ 2).totient = 67 * 66 := by
    simpa using Nat.totient_prime_pow (p := 67)
      (by norm_num) (n := 2) (by norm_num)
  have hbase : (((c : ℤ) : ZMod (67 ^ 2))) ^ (67 * 66) = 1 := by
    rw [hcunit.unit_spec] at hU
    simpa only [htotient] using hU
  push_cast
  rw [show 67 * (66 * t) = (67 * 66) * t by ring,
    pow_mul, hbase, one_pow]

/-! ## The vanishing polynomial -/

/-- The corrected relation polynomial.  Its third summand is the integral
power-basis representative of the algebraic `67^2` correction. -/
def vanishingRelationPolynomial67
    (P Q H : Polynomial ℤ) (C : ℤ) : Polynomial ℤ :=
  P - Polynomial.C C * Q - Polynomial.C (67 ^ 2 : ℤ) * H

/-- The exact source hinge preceding equation (3b): a deep unit relation
produces an integer polynomial which vanishes at `zeta` and whose value at
one is divisible by `67^2`. -/
theorem exists_vanishingRelationPolynomial67 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 67)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (a : SourceIndex 67 → ℤ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 134 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 67)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit67 hzeta i ^ a i) :
    ∃ H : Polynomial ℤ,
      let P := positiveRelationPolynomial67 (fun i ↦ (a i).toNat)
      let Q := positiveRelationPolynomial67 (fun i ↦ (-a i).toNat)
      let C : ℤ := c ^ (67 * (66 * t))
      let A := vanishingRelationPolynomial67 P Q H C
      Polynomial.aeval zeta A = 0 ∧
        (67 : ℤ) ^ 2 ∣ A.eval 1 := by
  let P := positiveRelationPolynomial67 (fun i ↦ (a i).toNat)
  let Q := positiveRelationPolynomial67 (fun i ↦ (-a i).toNat)
  let C : ℤ := c ^ (67 * (66 * t))
  have hpow := deep_power_congruence67 hzeta u c t hdeep
  obtain ⟨beta, hbeta⟩ := hpow
  have heval :=
    eval₂_positive_relation_of_relation hzeta u t a hrel
  have hPQ :
      Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger P -
          (C : 𝓞 K) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q =
        (67 : 𝓞 K) ^ 2 *
          (beta * Polynomial.eval₂ (Int.castRingHom (𝓞 K))
            hzeta.toInteger Q) := by
    dsimp only [P, Q]
    rw [heval]
    dsimp only [C]
    push_cast
    calc
      (u : 𝓞 K) ^ (66 * t) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q -
          (c : 𝓞 K) ^ (67 * (66 * t)) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q =
        ((u : 𝓞 K) ^ (66 * t) -
          (c : 𝓞 K) ^ (67 * (66 * t))) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q := by
              ring
      _ = (67 : 𝓞 K) ^ 2 *
          (beta * Polynomial.eval₂ (Int.castRingHom (𝓞 K))
            hzeta.toInteger Q) := by rw [hbeta]; ring
  obtain ⟨H, hH⟩ := hzeta.integralPowerBasis.exists_eq_aeval'
    (beta * Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q)
  refine ⟨H, ?_, ?_⟩
  · have hH' :
        beta * Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q =
          Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger H := by
      simpa only [Polynomial.aeval_def,
        IsPrimitiveRoot.integralPowerBasis_gen] using hH
    have hzeroO : Polynomial.aeval hzeta.toInteger
        (vanishingRelationPolynomial67 P Q H C) = 0 := by
      rw [Polynomial.aeval_def]
      change Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (vanishingRelationPolynomial67 P Q H C) = 0
      rw [vanishingRelationPolynomial67, Polynomial.eval₂_sub,
        Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hH']
      have hcast67 : (Int.castRingHom (𝓞 K)) (67 ^ 2 : ℤ) =
          (67 : 𝓞 K) ^ 2 := by norm_num
      rw [hcast67]
      exact sub_eq_zero.mpr hPQ
    have hzeroK := congrArg ((↑) : 𝓞 K → K) hzeroO
    change Polynomial.aeval zeta
      (vanishingRelationPolynomial67 P Q H C) = 0
    simpa [Polynomial.aeval_def] using hzeroK
  · have hPmod :=
      eval_one_positiveRelationPolynomial67_mod_sq
        (fun i ↦ (a i).toNat)
    have hQmod :=
      eval_one_positiveRelationPolynomial67_mod_sq
        (fun i ↦ (-a i).toNat)
    have hcnot := deep_integer_not_divisible67 hzeta u c hdeep
    have hCmod := deep_integer_power_mod_sq c t hcnot
    have hAmod :
        (((vanishingRelationPolynomial67 P Q H C).eval 1 : ℤ) :
          ZMod (67 ^ 2)) = 0 := by
      rw [vanishingRelationPolynomial67, eval_sub, eval_sub,
        eval_mul, eval_mul, eval_C, eval_C]
      push_cast
      dsimp only [P, Q, C] at hPmod hQmod hCmod ⊢
      rw [hPmod, hQmod, hCmod]
      have hsqzero : (4489 : ZMod (67 ^ 2)) = 0 := by
        simpa using ZMod.natCast_self 4489
      rw [hsqzero]
      ring
    have hdvd :
        (((67 ^ 2 : ℕ) : ℤ) ∣
          (vanishingRelationPolynomial67 P Q H C).eval 1) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAmod
    norm_num at hdvd ⊢
    exact hdvd

end

end Fermat.SixtySeven.VandiverDeepPolynomial
