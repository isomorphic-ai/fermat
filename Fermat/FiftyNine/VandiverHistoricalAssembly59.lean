import Fermat.FiftyNine.VandiverPreparedPair59
import Fermat.FiftyNine.VandiverLinearComparison59
import Fermat.FiftyNine.VandiverEquationEightAFactorization59
import Fermat.FiftyNine.VandiverLemmaTwo
import Fermat.FiftyNine.FirstCase
import Fermat.Cases

/-!
# Completion of Vandiver's historical proof at exponent 59

This file assembles the two normalized conjugate equation-(8) pairs, the
local equation-(10) congruence, the three quadratic identities, generator
coprimality, and the strict prime-support descent.  It proves the formerly
isolated `RealPrincipalGeneratorElimination59`, then combines it with the
fully formalized Vandiver Lemma II and Sophie Germain auxiliary prime 827
to obtain `Fermat.HoldsAt 59`.
-/

namespace Fermat.FiftyNine.VandiverHistorical

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverLemmaOne

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 59) K (by norm_num)

/-- The first trace unit `A+1` is real, just as the existing second trace
unit `A+2` is. -/
lemma equationTenTraceOneUnit_real59
    {ζ : K} (hζ : IsPrimitiveRoot ζ 59) :
    NumberField.IsCMField.unitsComplexConj K
        (equationTenTraceOneUnit59 hζ) =
      equationTenTraceOneUnit59 hζ := by
  apply Units.ext
  change NumberField.IsCMField.ringOfIntegersComplexConj K
      (equationTenTraceOneUnit59 hζ : 𝓞 K) =
    (equationTenTraceOneUnit59 hζ : 𝓞 K)
  rw [equationTenTraceOneUnit59_val, map_add,
    equationTenTraceOne_real59 hζ, map_one]

omit [NumberField K] [IsCyclotomicExtension {59} ℚ K] in
/-- Squaring historical equation (8a) gives the third quadratic input to
equation (10a). -/
lemma historicalEquationEightA_quadratic59
    {ζ : K} (hζ : IsPrimitiveRoot ζ 59)
    (s : HistoricalState hζ)
    (rhoZero : 𝓞 K) (etaZero : (𝓞 K)ˣ)
    (hzero :
      s.omega + s.theta =
        etaZero * kappa hζ ^ (59 * s.m - 29) * rhoZero ^ 59) :
    s.omega ^ 2 + 2 * (s.omega * s.theta) + s.theta ^ 2 =
      kappa hζ *
        ((etaZero ^ 2 : (𝓞 K)ˣ) *
          (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2) ^ 59) := by
  have hsquare := congrArg (fun x : 𝓞 K ↦ x ^ 2) hzero
  have hexp :
      (59 * s.m - 29) * 2 =
        (2 * s.m - 1) * 59 + 1 := by
    have hm := s.one_lt_m
    omega
  calc
    s.omega ^ 2 + 2 * (s.omega * s.theta) + s.theta ^ 2 =
        (s.omega + s.theta) ^ 2 := by ring
    _ = ((etaZero : 𝓞 K) *
          kappa hζ ^ (59 * s.m - 29) * rhoZero ^ 59) ^ 2 := hsquare
    _ = kappa hζ *
        ((etaZero ^ 2 : (𝓞 K)ˣ) *
          (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2) ^ 59) := by
      simp only [mul_pow, Units.val_pow_eq_pow_val, ← pow_mul]
      rw [hexp, pow_succ']
      ring

set_option maxRecDepth 5000 in
/-- Vandiver's source-faithful real-principal-generator elimination at
exponent 59.  This is the final concrete input required by the historical
well-founded descent. -/
theorem realPrincipalGeneratorElimination59
    {ζ : K} (hζ : IsPrimitiveRoot ζ 59) :
    RealPrincipalGeneratorElimination59 hζ := by
  intro s hs
  obtain ⟨rhoZero, etaZero, jZero, hzero, hgenerator,
      hconjZero, hetaZeroReal⟩ :=
    exists_historicalEquationEightA59 hζ s hs
  obtain ⟨dOne⟩ :=
    exists_preparedEquationEightPair_one59
      hζ s hs rhoZero etaZero hzero
  obtain ⟨dTwo⟩ :=
    exists_preparedEquationEightPair_two59
      hζ s hs rhoZero etaZero hzero
  let D : ℕ := (2 * s.m - 2) * 59
  have hcoefficient :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) * dOne.rplus ^ 59 -
          (dTwo.coefficient : 𝓞 K) * dTwo.rplus ^ 59 := by
    simpa only [D] using
      historicalEquationEight_one_two_coefficients_close59
        hζ s hs dOne.rplus dTwo.rplus
        dOne.coefficient dTwo.coefficient
        dOne.equation_plus dTwo.equation_plus
  have hpowOne :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        dOne.rplus ^ 59 - dOne.mu ^ 3481 := by
    have h := dOne.close_plus.trans
      (sub_dvd_pow_sub_pow dOne.rplus (dOne.mu ^ 59) 59)
    simpa only [D, ← pow_mul] using h
  have hpowTwo :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        dTwo.rplus ^ 59 - dTwo.mu ^ 3481 := by
    have h := dTwo.close_plus.trans
      (sub_dvd_pow_sub_pow dTwo.rplus (dTwo.mu ^ 59) 59)
    simpa only [D, ← pow_mul] using h
  have herrors :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) *
            (dOne.rplus ^ 59 - dOne.mu ^ 3481) -
          (dTwo.coefficient : 𝓞 K) *
            (dTwo.rplus ^ 59 - dTwo.mu ^ 3481) :=
    dvd_sub
      (dvd_mul_of_dvd_right hpowOne (dOne.coefficient : 𝓞 K))
      (dvd_mul_of_dvd_right hpowTwo (dTwo.coefficient : 𝓞 K))
  have hmuD :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) * dOne.mu ^ 3481 -
          (dTwo.coefficient : 𝓞 K) * dTwo.mu ^ 3481 := by
    have h := dvd_sub hcoefficient herrors
    convert h using 1
    ring
  have h118D : 118 ≤ D := by
    have hm := s.one_lt_m
    dsimp [D]
    omega
  have hmu118 :
      ((hζ.unit' : 𝓞 K) - 1) ^ 118 ∣
        (dOne.coefficient : 𝓞 K) * dOne.mu ^ 3481 -
          (dTwo.coefficient : 𝓞 K) * dTwo.mu ^ 3481 :=
    (pow_dvd_pow ((hζ.unit' : 𝓞 K) - 1) h118D).trans hmuD
  obtain ⟨c, hratio3481⟩ :=
    exists_int_ratio_pow3481_congruent59 hζ
      dOne.coefficient dTwo.coefficient dOne.mu dTwo.mu
      dOne.mu_real dTwo.mu_real dOne.mu_not_ramified hmu118
  obtain ⟨rationalBase, hnegativeRatio⟩ :=
    exists_int_negative_square_ratio_pow59_congruent59 hζ
      (dOne.coefficient / dTwo.coefficient) c hratio3481
  let minusOne : (𝓞 K)ˣ := -1
  let epsilonOne : (𝓞 K)ˣ :=
    minusOne *
      (equationTenTraceTwoUnit59 hζ * dOne.coefficient ^ 2)
  let epsilonTwo : (𝓞 K)ˣ :=
    equationTenTraceTwoUnit59 hζ * dTwo.coefficient ^ 2
  let epsilonThree : (𝓞 K)ˣ :=
    minusOne * (equationTenTraceOneUnit59 hζ * etaZero ^ 2)
  have hepsilonRatio :
      epsilonOne / epsilonTwo =
        -((dOne.coefficient / dTwo.coefficient) ^ 2) := by
    have hgroup :
        minusOne *
              (equationTenTraceTwoUnit59 hζ *
                dOne.coefficient ^ 2) /
            (equationTenTraceTwoUnit59 hζ *
              dTwo.coefficient ^ 2) =
          minusOne *
            (dOne.coefficient / dTwo.coefficient) ^ 2 := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        minusOne *
              (equationTenTraceTwoUnit59 hζ *
                dOne.coefficient ^ 2) *
              (dTwo.coefficient⁻¹ ^ 2 *
                (equationTenTraceTwoUnit59 hζ)⁻¹) =
            minusOne *
              (equationTenTraceTwoUnit59 hζ *
                (equationTenTraceTwoUnit59 hζ)⁻¹) *
              (dOne.coefficient ^ 2 *
                dTwo.coefficient⁻¹ ^ 2) := by ac_rfl
        _ = minusOne *
              (dOne.coefficient ^ 2 *
                dTwo.coefficient⁻¹ ^ 2) := by simp
        _ = minusOne *
              (dOne.coefficient * dTwo.coefficient⁻¹) ^ 2 := by
          rw [mul_pow]
    calc
      epsilonOne / epsilonTwo =
          minusOne *
                (equationTenTraceTwoUnit59 hζ *
                  dOne.coefficient ^ 2) /
              (equationTenTraceTwoUnit59 hζ *
                dTwo.coefficient ^ 2) := by
            rfl
      _ = minusOne *
          (dOne.coefficient / dTwo.coefficient) ^ 2 := hgroup
      _ = -((dOne.coefficient / dTwo.coefficient) ^ 2) := by
        dsimp [minusOne]
        ext
        simp
  have hhigh :
      ((1 : 𝓞 K) - hζ.unit') ^ 118 ∣
        (((epsilonOne / epsilonTwo : (𝓞 K)ˣ) : 𝓞 K) -
          (rationalBase : 𝓞 K) ^ 59) := by
    rw [hepsilonRatio]
    exact hnegativeRatio
  have hquadOne :=
    dOne.quadraticEquation_one hζ s
  have hquadTwo :=
    dTwo.quadraticEquation_two hζ s
  have hquadZero :=
    historicalEquationEightA_quadratic59
      hζ s rhoZero etaZero hzero
  have hweightedRaw :=
    equationTenB_commonKappa59 hζ s.omega s.theta
      (dOne.rplus * dOne.rminus)
      (dTwo.rplus * dTwo.rminus)
      (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2)
      (dOne.coefficient ^ 2)
      (equationTenTraceTwoUnit59 hζ * dTwo.coefficient ^ 2)
      (etaZero ^ 2)
      hquadOne hquadTwo hquadZero
  have hweighted :
      epsilonOne * (dOne.rplus * dOne.rminus) ^ 59 +
          epsilonTwo * (dTwo.rplus * dTwo.rminus) ^ 59 =
        epsilonThree *
          (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2) ^ 59 := by
    dsimp [epsilonOne, epsilonTwo, epsilonThree, minusOne]
    have hweightedRaw' := hweightedRaw
    simp only [Units.val_mul, Units.val_neg,
      Units.val_pow_eq_pow_val] at hweightedRaw'
    linear_combination -hweightedRaw'
  have hrhoZero : rhoZero ≠ 0 := by
    intro hrho
    apply historicalState_omega_add_theta_ne_zero59 hζ s
    rw [hzero, hrho]
    norm_num
  have hcop :=
    equationEight_generators_products_coprime59 hζ
      dOne.coefficient dOne.coefficient
      dTwo.coefficient dTwo.coefficient
      ((etaZero : 𝓞 K) * kappa hζ ^ (59 * s.m - 29))
      hrhoZero s.coprime_omega_theta
      dOne.equation_plus dOne.equation_minus
      dTwo.equation_plus dTwo.equation_minus
      hzero
      dOne.rplus_not_ramified dOne.rminus_not_ramified
      dTwo.rplus_not_ramified dTwo.rminus_not_ramified
  have hminusOneReal :
      NumberField.IsCMField.unitsComplexConj K minusOne =
        minusOne := by
    dsimp [minusOne]
    apply Units.ext
    change NumberField.IsCMField.ringOfIntegersComplexConj K
        (-1 : 𝓞 K) = -1
    rw [map_neg, map_one]
  have hepsilonThreeReal :
      NumberField.IsCMField.unitsComplexConj K epsilonThree =
        epsilonThree := by
    dsimp [epsilonThree]
    rw [map_mul, hminusOneReal, map_mul,
      equationTenTraceOneUnit_real59 hζ, hetaZeroReal]
  have hepsilonTwoReal :
      NumberField.IsCMField.unitsComplexConj K epsilonTwo =
        epsilonTwo := by
    dsimp [epsilonTwo]
    rw [map_mul, map_pow,
      equationTenTraceTwoUnit_real59 hζ, dTwo.coefficient_real]
  have hrealEta :
      NumberField.IsCMField.unitsComplexConj K
          (epsilonThree / epsilonTwo) =
        epsilonThree / epsilonTwo := by
    rw [map_div, hepsilonThreeReal, hepsilonTwoReal]
  exact ⟨
    { x := dOne.rplus * dOne.rminus
      y := dTwo.rplus * dTwo.rminus
      z := rhoZero ^ 2
      epsilon₁ := epsilonOne
      epsilon₂ := epsilonTwo
      epsilon₃ := epsilonThree
      rationalBase := rationalBase
      highCongruence := hhigh
      weightedEquation := hweighted
      z_ne_zero := hcop.1
      coprime_xy := hcop.2.1
      coprime_yz := hcop.2.2.1
      coprime_xz := hcop.2.2.2
      conjugationExponent_x := 0
      conjugationExponent_y := 0
      conjugationExponent_z := jZero
      conjugation_x := by
        simpa using dOne.product_real hζ s hζ.unit'
      conjugation_y := by
        simpa using dTwo.product_real hζ s (hζ.unit' ^ 2)
      conjugation_z := hconjZero
      real_eta := hrealEta
      factorSupport_strict :=
        historicalEquationEightA_square_support_strict_unconditional59
          hζ s hs rhoZero hgenerator }⟩

end

end Fermat.FiftyNine.VandiverHistorical

namespace Fermat.FiftyNine

open scoped NumberField nonZeroDivisors Cyclotomic

/-- Vandiver's historical proof excludes the second case at exponent 59,
with the cyclotomic field and primitive root chosen canonically. -/
theorem secondCaseExcluded_fiftyNine :
    Fermat.SecondCaseExcluded 59 := by
  letI : NeZero (59 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {59} ℚ (CyclotomicField 59 ℚ) :=
    CyclotomicField.isCyclotomicExtension 59 ℚ
  obtain ⟨zeta, hzeta⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 59 ℚ)
      (Set.mem_singleton 59) (by norm_num : 59 ≠ 0)
  intro a b c ha hb hc hgcd hdiv
  exact
    (VandiverHistorical.secondCaseExcluded_59_of_vandiverLemmaTwo
      (K := CyclotomicField 59 ℚ) (ζ := zeta)
      hzeta
      (VandiverHistorical.realPrincipalGeneratorElimination59
        (K := CyclotomicField 59 ℚ) hzeta)
      (VandiverLemmaTwo.vandiverLemmaTwo_fiftyNine
        (K := CyclotomicField 59 ℚ)))
      ha hb hc hgcd hdiv

/-- Fermat's Last Theorem at exponent 59. -/
theorem holdsAt_fiftyNine : Fermat.HoldsAt 59 := by
  exact Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    (by norm_num) (by norm_num) (by norm_num)
    noConsecutivePowers_59_827 exponentNotPower_59_827
    secondCaseExcluded_fiftyNine

end Fermat.FiftyNine
