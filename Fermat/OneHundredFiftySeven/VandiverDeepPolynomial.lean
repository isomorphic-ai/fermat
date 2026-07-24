import Fermat.Irregular.VandiverPolynomialRemainder
import Fermat.Irregular.VandiverUnitLemma
import Fermat.OneHundredFiftySeven.VandiverPolynomialUnits

/-!
# From Vandiver's deep congruence to the polynomial remainder at 157

This file formalizes the passage from Vandiver's local hypothesis

`u ≡ c^157 mod (1 - zeta)^314`

and an exponent relation among the actual diagonal units to the integer
polynomial used in equations (3b)--(3d).

Integer exponents have already been cleared into a positive numerator `P`
and denominator `Q` in `VandiverPolynomialUnits`.  Here we prove:

* the deep congruence implies a congruence modulo `157^2`;
* the integer `c` is prime to `157`;
* the normalizations `226^156` and `c^(157*156*t)` are `1` modulo `157^2`;
* the resulting algebraic correction is represented by an integer
  polynomial using the integral power basis; and
* the polynomial

  `A = P - C*Cpoly*Q - C*(157^2)*H`

  vanishes at `zeta` and satisfies `157^2 ∣ A(1)`.

The generic polynomial-remainder and high-derivative theorems can therefore
be applied without assuming any part of Vandiver's conclusion.
-/

open scoped BigOperators NumberField

namespace Fermat.OneHundredFiftySeven.VandiverDeepPolynomial

noncomputable section

open Polynomial
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.OneHundredFiftySeven.VandiverPolynomialUnits
open Fermat.OneHundredFiftySeven.VandiverDiagonalUnits

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

set_option maxRecDepth 100000

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {157} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 157) K (by norm_num)

/-- One hundred thirty-four powers of the cyclotomic uniformizer contain two powers
of the rational prime. -/
theorem oneHundredFiftySeven_sq_dvd_of_deep {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157) (x : 𝓞 K)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 314 ∣ x) :
    (157 : 𝓞 K) ^ 2 ∣ x := by
  have hbase : (hzeta.unit' : 𝓞 K) - 1 ∣
      (1 : 𝓞 K) - hzeta.unit' := by
    refine ⟨-1, ?_⟩
    ring
  have h132 : ((hzeta.unit' : 𝓞 K) - 1) ^ 312 ∣ x :=
    (pow_dvd_pow_of_dvd hbase 312).trans
      ((pow_dvd_pow ((1 : 𝓞 K) - hzeta.unit') (by omega)).trans hdeep)
  have hp := (associated_zeta_sub_one_pow_prime hzeta).pow_pow (n := 2)
  have hExp312 : (157 - 1 : ℕ) * 2 = 312 := by norm_num
  have hCast157 : (((157 : ℕ) : 𝓞 K)) = (157 : 𝓞 K) := by norm_num
  have hp' : Associated (((hzeta.unit' : 𝓞 K) - 1) ^ 312)
      ((157 : 𝓞 K) ^ 2) := by
    simpa only [← pow_mul, hExp312, hCast157] using hp
  exact hp'.dvd_iff_dvd_left.mp h132

/-- Raising a deeply congruent unit to Vandiver's outer exponent preserves
the congruence modulo `157^2`. -/
theorem deep_power_congruence157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 314 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 157) :
    (157 : 𝓞 K) ^ 2 ∣
      (u : 𝓞 K) ^ (156 * t) -
        (c : 𝓞 K) ^ (157 * (156 * t)) := by
  have hbase : (157 : 𝓞 K) ^ 2 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 157 :=
    oneHundredFiftySeven_sq_dvd_of_deep hzeta _ hdeep
  have hpow := hbase.trans
    (sub_dvd_pow_sub_pow (u : 𝓞 K) ((c : 𝓞 K) ^ 157) (156 * t))
  convert hpow using 1
  rw [← pow_mul]

/-- The integer in a deep unit congruence cannot be divisible by `157`.
Otherwise the cyclotomic uniformizer would divide a unit. -/
theorem deep_integer_not_divisible157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157)
    (u : (𝓞 K)ˣ) (c : ℤ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 314 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 157) :
    ¬(157 : ℤ) ∣ c := by
  intro hc
  let pi : 𝓞 K := (hzeta.unit' : 𝓞 K) - 1
  have h156 : (157 - 1 : ℕ) = 156 := by norm_num
  have hCast157 : (((157 : ℕ) : 𝓞 K)) = (157 : 𝓞 K) := by norm_num
  have hpipow : pi ^ 156 ∣ (157 : 𝓞 K) := by
    simpa only [pi, h156, hCast157] using
      (associated_zeta_sub_one_pow_prime hzeta).dvd
  have hpi157 : pi ∣ (157 : 𝓞 K) :=
    (dvd_pow_self pi (by norm_num : (156 : ℕ) ≠ 0)).trans hpipow
  obtain ⟨d, rfl⟩ := hc
  have hpic : pi ∣ (((157 : ℤ) * d : ℤ) : 𝓞 K) := by
    push_cast
    exact dvd_mul_of_dvd_left hpi157 _
  have hpicpow : pi ∣ ((((157 : ℤ) * d : ℤ) : 𝓞 K) ^ 157) :=
    hpic.trans (dvd_pow_self _ (by norm_num : (157 : ℕ) ≠ 0))
  have hpideep : pi ∣
      (u : 𝓞 K) - ((((157 : ℤ) * d : ℤ) : 𝓞 K) ^ 157) := by
    have hbase : pi ∣ (1 : 𝓞 K) - hzeta.unit' := by
      refine ⟨-1, ?_⟩
      dsimp [pi]
      ring
    exact hbase.trans
      ((dvd_pow_self ((1 : 𝓞 K) - hzeta.unit')
        (by norm_num : (314 : ℕ) ≠ 0)).trans hdeep)
  have hpiu : pi ∣ (u : 𝓞 K) := by
    convert dvd_add hpideep hpicpow using 1
    ring
  exact hzeta.zeta_sub_one_prime'.not_unit
    (isUnit_of_dvd_unit hpiu u.isUnit)

/-! ## Evaluation at one modulo `157^2` -/

/-- The source's chosen Teichmüller representative satisfies
`226^156 = 1 mod 157^2`. -/
theorem teichmuller226_pow_oneHundredFiftySix :
    (226 : ZMod (157 ^ 2)) ^ 156 = 1 := by
  have hdvd : (24649 : ℤ) ∣ (226 : ℤ) ^ 156 - 1 := by norm_num
  have hz : ((((226 : ℤ) ^ 156 - 1 : ℤ)) : ZMod (157 ^ 2)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa using hdvd)
  push_cast at hz
  exact sub_eq_zero.mp hz

/-- Every basic Vandiver polynomial takes the value `226` at `1`. -/
theorem eval_one_basicVandiverPolynomial157 (s : ℕ) :
    (basicVandiverPolynomial157 s).eval 1 = 226 := by
  rw [basicVandiverPolynomial157, eval_mul, eval_pow, eval_X,
    eval_finsetSum]
  norm_num [Finset.sum_const]

/-- The value at one of every diagonal polynomial has 66th power one
modulo `157^2`. -/
theorem eval_one_diagonal_pow_oneHundredFiftySix
    (i : SourceIndex 157) :
    ((((diagonalVandiverPolynomial157 i).eval 1 : ℤ) :
      ZMod (157 ^ 2))) ^ 156 = 1 := by
  rw [diagonalVandiverPolynomial157, eval_prod]
  change ((Int.castRingHom (ZMod (157 ^ 2)))
      (∏ j, (basicVandiverPolynomial157 (conjugateExponent157 j) ^
        diagonalWeight157 i j).eval 1)) ^ 156 = 1
  rw [map_prod]
  rw [← Finset.prod_pow Finset.univ 156
    (fun j ↦ (Int.castRingHom (ZMod (157 ^ 2)))
      ((basicVandiverPolynomial157 (conjugateExponent157 j) ^
        diagonalWeight157 i j).eval 1))]
  apply Finset.prod_eq_one
  intro j hj
  rw [eval_pow, map_pow, eval_one_basicVandiverPolynomial157]
  calc
    (((226 : ZMod (157 ^ 2)) ^ diagonalWeight157 i j) ^ 156) =
        ((226 : ZMod (157 ^ 2)) ^ 156) ^ diagonalWeight157 i j := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega
    _ = 1 := by rw [teichmuller226_pow_oneHundredFiftySix, one_pow]

/-- Every positive relation polynomial is `1` at one modulo `157^2`.
The outer exponent `156` is essential here. -/
theorem eval_one_positiveRelationPolynomial157_mod_sq
    (b : SourceIndex 157 → ℕ) :
    (((positiveRelationPolynomial157 b).eval 1 : ℤ) :
      ZMod (157 ^ 2)) = 1 := by
  rw [positiveRelationPolynomial157, eval_prod]
  change (Int.castRingHom (ZMod (157 ^ 2)))
      (∏ i, (diagonalVandiverPolynomial157 i ^ (156 * b i)).eval 1) = 1
  rw [map_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [eval_pow, map_pow]
  change ((((diagonalVandiverPolynomial157 i).eval 1 : ℤ) :
      ZMod (157 ^ 2)) ^ (156 * b i)) = 1
  rw [pow_mul, eval_one_diagonal_pow_oneHundredFiftySix, one_pow]

/-- Euler's theorem at modulus `157^2`, in precisely the exponent appearing
in the denominator-cleared unit relation. -/
theorem deep_integer_power_mod_sq
    (c : ℤ) (t : ℕ) (hc : ¬(157 : ℤ) ∣ c) :
    ((c ^ (157 * (156 * t)) : ℤ) : ZMod (157 ^ 2)) = 1 := by
  let m := c.natAbs
  have hmnot : ¬157 ∣ m := by
    intro hm
    apply hc
    rw [← Int.natAbs_dvd_natAbs]
    norm_num [m]
    exact hm
  have hcop157 : m.Coprime 157 :=
    ((show Nat.Prime 157 by norm_num).coprime_iff_not_dvd.mpr hmnot).symm
  have hcop : m.Coprime (157 ^ 2) := hcop157.pow_right 2
  have hmunit : IsUnit (m : ZMod (157 ^ 2)) :=
    (ZMod.isUnit_iff_coprime m (157 ^ 2)).mpr hcop
  have hcunit : IsUnit ((c : ℤ) : ZMod (157 ^ 2)) := by
    rcases Int.natAbs_eq c with h | h
    · rw [h]
      push_cast
      simpa [m] using hmunit
    · rw [h]
      push_cast
      simpa [m] using hmunit.neg
  let U : (ZMod (157 ^ 2))ˣ := hcunit.unit
  have hU : ((U : ZMod (157 ^ 2)) ^ (157 ^ 2).totient) = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg ((↑) : (ZMod (157 ^ 2))ˣ → ZMod (157 ^ 2))
        (ZMod.pow_totient U)
  have htotient : (157 ^ 2).totient = 157 * 156 := by
    simpa using Nat.totient_prime_pow (p := 157)
      (by norm_num) (n := 2) (by norm_num)
  have hbase : (((c : ℤ) : ZMod (157 ^ 2))) ^ (157 * 156) = 1 := by
    rw [hcunit.unit_spec] at hU
    simpa only [htotient] using hU
  push_cast
  rw [show 157 * (156 * t) = (157 * 156) * t by ring,
    pow_mul, hbase, one_pow]

/-! ## The vanishing polynomial -/

/-- The corrected relation polynomial.  Its third summand is the integral
power-basis representative of the algebraic `157^2` correction. -/
def vanishingRelationPolynomial157
    (P Q H : Polynomial ℤ) (C : ℤ) : Polynomial ℤ :=
  P - Polynomial.C C * Q - Polynomial.C (157 ^ 2 : ℤ) * H

/-- The exact source hinge preceding equation (3b): a deep unit relation
produces an integer polynomial which vanishes at `zeta` and whose value at
one is divisible by `157^2`. -/
theorem exists_vanishingRelationPolynomial157 {zeta : K}
    (hzeta : IsPrimitiveRoot zeta 157)
    (u : (𝓞 K)ˣ) (c : ℤ) (t : ℕ)
    (a : SourceIndex 157 → ℤ)
    (hdeep : ((1 : 𝓞 K) - hzeta.unit') ^ 314 ∣
      (u : 𝓞 K) - (c : 𝓞 K) ^ 157)
    (hrel : u ^ t =
      ∏ i, diagonalVandiverUnit157 hzeta i ^ a i) :
    ∃ H : Polynomial ℤ,
      let P := positiveRelationPolynomial157 (fun i ↦ (a i).toNat)
      let Q := positiveRelationPolynomial157 (fun i ↦ (-a i).toNat)
      let C : ℤ := c ^ (157 * (156 * t))
      let A := vanishingRelationPolynomial157 P Q H C
      Polynomial.aeval zeta A = 0 ∧
        (157 : ℤ) ^ 2 ∣ A.eval 1 := by
  let P := positiveRelationPolynomial157 (fun i ↦ (a i).toNat)
  let Q := positiveRelationPolynomial157 (fun i ↦ (-a i).toNat)
  let C : ℤ := c ^ (157 * (156 * t))
  have hpow := deep_power_congruence157 hzeta u c t hdeep
  obtain ⟨beta, hbeta⟩ := hpow
  have heval :=
    eval₂_positive_relation_of_relation hzeta u t a hrel
  have hPQ :
      Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger P -
          (C : 𝓞 K) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q =
        (157 : 𝓞 K) ^ 2 *
          (beta * Polynomial.eval₂ (Int.castRingHom (𝓞 K))
            hzeta.toInteger Q) := by
    dsimp only [P, Q]
    rw [heval]
    dsimp only [C]
    push_cast
    calc
      (u : 𝓞 K) ^ (156 * t) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q -
          (c : 𝓞 K) ^ (157 * (156 * t)) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q =
        ((u : 𝓞 K) ^ (156 * t) -
          (c : 𝓞 K) ^ (157 * (156 * t))) *
            Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger Q := by
              ring
      _ = (157 : 𝓞 K) ^ 2 *
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
        (vanishingRelationPolynomial157 P Q H C) = 0 := by
      rw [Polynomial.aeval_def]
      change Polynomial.eval₂ (Int.castRingHom (𝓞 K)) hzeta.toInteger
        (vanishingRelationPolynomial157 P Q H C) = 0
      rw [vanishingRelationPolynomial157, Polynomial.eval₂_sub,
        Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_C, ← hH']
      have hcast157 : (Int.castRingHom (𝓞 K)) (157 ^ 2 : ℤ) =
          (157 : 𝓞 K) ^ 2 := by norm_num
      rw [hcast157]
      exact sub_eq_zero.mpr hPQ
    have hzeroK := congrArg ((↑) : 𝓞 K → K) hzeroO
    change Polynomial.aeval zeta
      (vanishingRelationPolynomial157 P Q H C) = 0
    simpa [Polynomial.aeval_def] using hzeroK
  · have hPmod :=
      eval_one_positiveRelationPolynomial157_mod_sq
        (fun i ↦ (a i).toNat)
    have hQmod :=
      eval_one_positiveRelationPolynomial157_mod_sq
        (fun i ↦ (-a i).toNat)
    have hcnot := deep_integer_not_divisible157 hzeta u c hdeep
    have hCmod := deep_integer_power_mod_sq c t hcnot
    have hAmod :
        (((vanishingRelationPolynomial157 P Q H C).eval 1 : ℤ) :
          ZMod (157 ^ 2)) = 0 := by
      rw [vanishingRelationPolynomial157, eval_sub, eval_sub,
        eval_mul, eval_mul, eval_C, eval_C]
      push_cast
      dsimp only [P, Q, C] at hPmod hQmod hCmod ⊢
      rw [hPmod, hQmod, hCmod]
      have hsqzero : (24649 : ZMod (157 ^ 2)) = 0 := by
        simpa using ZMod.natCast_self 24649
      rw [hsqzero]
      ring
    have hdvd :
        (((157 ^ 2 : ℕ) : ℤ) ∣
          (vanishingRelationPolynomial157 P Q H C).eval 1) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAmod
    norm_num at hdvd ⊢
    exact hdvd

end

end Fermat.OneHundredFiftySeven.VandiverDeepPolynomial
