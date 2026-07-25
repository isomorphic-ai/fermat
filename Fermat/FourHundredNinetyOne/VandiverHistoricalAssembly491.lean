import Fermat.FourHundredNinetyOne.VandiverPreparedPair491
import Fermat.FourHundredNinetyOne.VandiverLinearComparison491
import Fermat.FourHundredNinetyOne.VandiverEquationEightAFactorization491
import Fermat.FourHundredNinetyOne.VandiverLemmaTwo
import Fermat.FourHundredNinetyOne.FirstCase
import Fermat.Cases

/-!
# Completion of Vandiver's historical proof at exponent 491

This file assembles the two normalized conjugate equation-(8) pairs, the
local equation-(10) congruence, the three quadratic identities, generator
coprimality, and the strict prime-support descent.  It proves the formerly
isolated `RealPrincipalGeneratorElimination491`, then combines it with the
fully formalized Vandiver Lemma II and Sophie Germain auxiliary prime 983
to obtain `Fermat.HoldsAt 491`.
-/

namespace Fermat.FourHundredNinetyOne.VandiverHistorical

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverLemmaOne

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {491} ℚ K]

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 491) K (by norm_num)

/-- The first trace unit `A+1` is real, just as the existing second trace
unit `A+2` is. -/
lemma equationTenTraceOneUnit_real491
    {ζ : K} (hζ : IsPrimitiveRoot ζ 491) :
    NumberField.IsCMField.unitsComplexConj K
        (equationTenTraceOneUnit491 hζ) =
      equationTenTraceOneUnit491 hζ := by
  apply Units.ext
  change NumberField.IsCMField.ringOfIntegersComplexConj K
      (equationTenTraceOneUnit491 hζ : 𝓞 K) =
    (equationTenTraceOneUnit491 hζ : 𝓞 K)
  rw [equationTenTraceOneUnit491_val, map_add,
    equationTenTraceOne_real491 hζ, map_one]

omit [NumberField K] [IsCyclotomicExtension {491} ℚ K] in
/-- Squaring historical equation (8a) gives the third quadratic input to
equation (10a). -/
lemma historicalEquationEightA_quadratic491
    {ζ : K} (hζ : IsPrimitiveRoot ζ 491)
    (s : HistoricalState hζ)
    (rhoZero : 𝓞 K) (etaZero : (𝓞 K)ˣ)
    (hzero :
      s.omega + s.theta =
        etaZero * kappa hζ ^ (491 * s.m - 245) * rhoZero ^ 491) :
    s.omega ^ 2 + 2 * (s.omega * s.theta) + s.theta ^ 2 =
      kappa hζ *
        ((etaZero ^ 2 : (𝓞 K)ˣ) *
          (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2) ^ 491) := by
  have hsquare := congrArg (fun x : 𝓞 K ↦ x ^ 2) hzero
  have hexp :
      (491 * s.m - 245) * 2 =
        (2 * s.m - 1) * 491 + 1 := by
    have hm := s.one_lt_m
    omega
  calc
    s.omega ^ 2 + 2 * (s.omega * s.theta) + s.theta ^ 2 =
        (s.omega + s.theta) ^ 2 := by ring
    _ = ((etaZero : 𝓞 K) *
          kappa hζ ^ (491 * s.m - 245) * rhoZero ^ 491) ^ 2 := hsquare
    _ = kappa hζ *
        ((etaZero ^ 2 : (𝓞 K)ˣ) *
          (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2) ^ 491) := by
      simp only [mul_pow, Units.val_pow_eq_pow_val, ← pow_mul]
      rw [hexp, pow_succ']
      ring

set_option maxRecDepth 50000 in
/-- Vandiver's source-faithful real-principal-generator elimination at
exponent 491.  This is the final concrete input required by the historical
well-founded descent. -/
theorem realPrincipalGeneratorElimination491
    {ζ : K} (hζ : IsPrimitiveRoot ζ 491) :
    RealPrincipalGeneratorElimination491 hζ := by
  intro s hs
  obtain ⟨rhoZero, etaZero, jZero, hzero, hgenerator,
      hconjZero, hetaZeroReal⟩ :=
    exists_historicalEquationEightA491 hζ s hs
  obtain ⟨dOne⟩ :=
    exists_preparedEquationEightPair_one491
      hζ s hs rhoZero etaZero hzero
  obtain ⟨dTwo⟩ :=
    exists_preparedEquationEightPair_two491
      hζ s hs rhoZero etaZero hzero
  let D : ℕ := (2 * s.m - 2) * 491
  have hcoefficient :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) * dOne.rplus ^ 491 -
          (dTwo.coefficient : 𝓞 K) * dTwo.rplus ^ 491 := by
    simpa only [D] using
      historicalEquationEight_one_two_coefficients_close491
        hζ s hs dOne.rplus dTwo.rplus
        dOne.coefficient dTwo.coefficient
        dOne.equation_plus dTwo.equation_plus
  have hpowOne :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        dOne.rplus ^ 491 - dOne.mu ^ 241081 := by
    have h := dOne.close_plus.trans
      (sub_dvd_pow_sub_pow dOne.rplus (dOne.mu ^ 491) 491)
    simpa only [D, ← pow_mul] using h
  have hpowTwo :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        dTwo.rplus ^ 491 - dTwo.mu ^ 241081 := by
    have h := dTwo.close_plus.trans
      (sub_dvd_pow_sub_pow dTwo.rplus (dTwo.mu ^ 491) 491)
    simpa only [D, ← pow_mul] using h
  have herrors :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) *
            (dOne.rplus ^ 491 - dOne.mu ^ 241081) -
          (dTwo.coefficient : 𝓞 K) *
            (dTwo.rplus ^ 491 - dTwo.mu ^ 241081) :=
    dvd_sub
      (dvd_mul_of_dvd_right hpowOne (dOne.coefficient : 𝓞 K))
      (dvd_mul_of_dvd_right hpowTwo (dTwo.coefficient : 𝓞 K))
  have hmuD :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) * dOne.mu ^ 241081 -
          (dTwo.coefficient : 𝓞 K) * dTwo.mu ^ 241081 := by
    have h := dvd_sub hcoefficient herrors
    convert h using 1
    ring
  have h982D : 982 ≤ D := by
    have hm := s.one_lt_m
    dsimp [D]
    omega
  have hmu982 :
      ((hζ.unit' : 𝓞 K) - 1) ^ 982 ∣
        (dOne.coefficient : 𝓞 K) * dOne.mu ^ 241081 -
          (dTwo.coefficient : 𝓞 K) * dTwo.mu ^ 241081 :=
    (pow_dvd_pow ((hζ.unit' : 𝓞 K) - 1) h982D).trans hmuD
  obtain ⟨c, hratio241081⟩ :=
    exists_int_ratio_pow241081_congruent491 hζ
      dOne.coefficient dTwo.coefficient dOne.mu dTwo.mu
      dOne.mu_real dTwo.mu_real dOne.mu_not_ramified hmu982
  obtain ⟨rationalBase, hnegativeRatio⟩ :=
    exists_int_negative_square_ratio_pow491_congruent491 hζ
      (dOne.coefficient / dTwo.coefficient) c hratio241081
  let minusOne : (𝓞 K)ˣ := -1
  let epsilonOne : (𝓞 K)ˣ :=
    minusOne *
      (equationTenTraceTwoUnit491 hζ * dOne.coefficient ^ 2)
  let epsilonTwo : (𝓞 K)ˣ :=
    equationTenTraceTwoUnit491 hζ * dTwo.coefficient ^ 2
  let epsilonThree : (𝓞 K)ˣ :=
    minusOne * (equationTenTraceOneUnit491 hζ * etaZero ^ 2)
  have hepsilonRatio :
      epsilonOne / epsilonTwo =
        -((dOne.coefficient / dTwo.coefficient) ^ 2) := by
    have hgroup :
        minusOne *
              (equationTenTraceTwoUnit491 hζ *
                dOne.coefficient ^ 2) /
            (equationTenTraceTwoUnit491 hζ *
              dTwo.coefficient ^ 2) =
          minusOne *
            (dOne.coefficient / dTwo.coefficient) ^ 2 := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        minusOne *
              (equationTenTraceTwoUnit491 hζ *
                dOne.coefficient ^ 2) *
              (dTwo.coefficient⁻¹ ^ 2 *
                (equationTenTraceTwoUnit491 hζ)⁻¹) =
            minusOne *
              (equationTenTraceTwoUnit491 hζ *
                (equationTenTraceTwoUnit491 hζ)⁻¹) *
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
                (equationTenTraceTwoUnit491 hζ *
                  dOne.coefficient ^ 2) /
              (equationTenTraceTwoUnit491 hζ *
                dTwo.coefficient ^ 2) := by
            rfl
      _ = minusOne *
          (dOne.coefficient / dTwo.coefficient) ^ 2 := hgroup
      _ = -((dOne.coefficient / dTwo.coefficient) ^ 2) := by
        dsimp [minusOne]
        ext
        simp
  have hhigh :
      ((1 : 𝓞 K) - hζ.unit') ^ 982 ∣
        (((epsilonOne / epsilonTwo : (𝓞 K)ˣ) : 𝓞 K) -
          (rationalBase : 𝓞 K) ^ 491) := by
    rw [hepsilonRatio]
    exact hnegativeRatio
  have hquadOne :=
    dOne.quadraticEquation_one hζ s
  have hquadTwo :=
    dTwo.quadraticEquation_two hζ s
  have hquadZero :=
    historicalEquationEightA_quadratic491
      hζ s rhoZero etaZero hzero
  have hweightedRaw :=
    equationTenB_commonKappa491 hζ s.omega s.theta
      (dOne.rplus * dOne.rminus)
      (dTwo.rplus * dTwo.rminus)
      (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2)
      (dOne.coefficient ^ 2)
      (equationTenTraceTwoUnit491 hζ * dTwo.coefficient ^ 2)
      (etaZero ^ 2)
      hquadOne hquadTwo hquadZero
  have hweighted :
      epsilonOne * (dOne.rplus * dOne.rminus) ^ 491 +
          epsilonTwo * (dTwo.rplus * dTwo.rminus) ^ 491 =
        epsilonThree *
          (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2) ^ 491 := by
    dsimp [epsilonOne, epsilonTwo, epsilonThree, minusOne]
    have hweightedRaw' := hweightedRaw
    simp only [Units.val_mul, Units.val_neg,
      Units.val_pow_eq_pow_val] at hweightedRaw'
    linear_combination -hweightedRaw'
  have hrhoZero : rhoZero ≠ 0 := by
    intro hrho
    apply historicalState_omega_add_theta_ne_zero491 hζ s
    rw [hzero, hrho]
    norm_num
  have hcop :=
    equationEight_generators_products_coprime491 hζ
      dOne.coefficient dOne.coefficient
      dTwo.coefficient dTwo.coefficient
      ((etaZero : 𝓞 K) * kappa hζ ^ (491 * s.m - 245))
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
      equationTenTraceOneUnit_real491 hζ, hetaZeroReal]
  have hepsilonTwoReal :
      NumberField.IsCMField.unitsComplexConj K epsilonTwo =
        epsilonTwo := by
    dsimp [epsilonTwo]
    rw [map_mul, map_pow,
      equationTenTraceTwoUnit_real491 hζ, dTwo.coefficient_real]
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
        historicalEquationEightA_square_support_strict_unconditional491
          hζ s hs rhoZero hgenerator }⟩

end

end Fermat.FourHundredNinetyOne.VandiverHistorical

namespace Fermat.FourHundredNinetyOne

open scoped NumberField nonZeroDivisors Cyclotomic

/-- Vandiver's historical proof excludes the second case at exponent 491,
with the cyclotomic field and primitive root chosen canonically. -/
theorem secondCaseExcluded_fourHundredNinetyOne :
    Fermat.SecondCaseExcluded 491 := by
  letI : NeZero (491 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {491} ℚ (CyclotomicField 491 ℚ) :=
    CyclotomicField.isCyclotomicExtension 491 ℚ
  obtain ⟨zeta, hzeta⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 491 ℚ)
      (Set.mem_singleton 491) (by norm_num : 491 ≠ 0)
  intro a b c ha hb hc hgcd hdiv
  exact
    (VandiverHistorical.secondCaseExcluded_491_of_vandiverLemmaTwo
      (K := CyclotomicField 491 ℚ) (ζ := zeta)
      hzeta
      (VandiverHistorical.realPrincipalGeneratorElimination491
        (K := CyclotomicField 491 ℚ) hzeta)
      (VandiverLemmaTwo.vandiverLemmaTwo_fourHundredNinetyOne
        (K := CyclotomicField 491 ℚ)))
      ha hb hc hgcd hdiv

/-- Fermat's Last Theorem at exponent 491. -/
theorem holdsAt_fourHundredNinetyOne : Fermat.HoldsAt 491 := by
  exact Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    (by norm_num) (by norm_num) (by norm_num)
    noConsecutivePowers_491_983 exponentNotPower_491_983
    secondCaseExcluded_fourHundredNinetyOne

end Fermat.FourHundredNinetyOne
