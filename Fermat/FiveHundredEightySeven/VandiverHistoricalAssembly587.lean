import Fermat.FiveHundredEightySeven.VandiverPreparedPair587
import Fermat.FiveHundredEightySeven.VandiverLinearComparison587
import Fermat.FiveHundredEightySeven.VandiverEquationEightAFactorization587
import Fermat.FiveHundredEightySeven.VandiverLemmaTwo
import Fermat.FiveHundredEightySeven.FirstCase
import Fermat.Cases

/-!
# Completion of Vandiver's historical proof at exponent 587

This file assembles the two normalized conjugate equation-(8) pairs, the
local equation-(10) congruence, the three quadratic identities, generator
coprimality, and the strict prime-support descent.  It proves the formerly
isolated `RealPrincipalGeneratorElimination587`, then combines it with the
fully formalized Vandiver Lemma II and Sophie Germain auxiliary prime 8219
to obtain `Fermat.HoldsAt 587`.
-/

namespace Fermat.FiveHundredEightySeven.VandiverHistorical

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverLemmaOne

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {587} ℚ K]

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 587) K (by norm_num)

/-- The first trace unit `A+1` is real, just as the existing second trace
unit `A+2` is. -/
lemma equationTenTraceOneUnit_real587
    {ζ : K} (hζ : IsPrimitiveRoot ζ 587) :
    NumberField.IsCMField.unitsComplexConj K
        (equationTenTraceOneUnit587 hζ) =
      equationTenTraceOneUnit587 hζ := by
  apply Units.ext
  change NumberField.IsCMField.ringOfIntegersComplexConj K
      (equationTenTraceOneUnit587 hζ : 𝓞 K) =
    (equationTenTraceOneUnit587 hζ : 𝓞 K)
  rw [equationTenTraceOneUnit587_val, map_add,
    equationTenTraceOne_real587 hζ, map_one]

omit [NumberField K] [IsCyclotomicExtension {587} ℚ K] in
/-- Squaring historical equation (8a) gives the third quadratic input to
equation (10a). -/
lemma historicalEquationEightA_quadratic587
    {ζ : K} (hζ : IsPrimitiveRoot ζ 587)
    (s : HistoricalState hζ)
    (rhoZero : 𝓞 K) (etaZero : (𝓞 K)ˣ)
    (hzero :
      s.omega + s.theta =
        etaZero * kappa hζ ^ (587 * s.m - 293) * rhoZero ^ 587) :
    s.omega ^ 2 + 2 * (s.omega * s.theta) + s.theta ^ 2 =
      kappa hζ *
        ((etaZero ^ 2 : (𝓞 K)ˣ) *
          (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2) ^ 587) := by
  have hsquare := congrArg (fun x : 𝓞 K ↦ x ^ 2) hzero
  have hexp :
      (587 * s.m - 293) * 2 =
        (2 * s.m - 1) * 587 + 1 := by
    have hm := s.one_lt_m
    omega
  calc
    s.omega ^ 2 + 2 * (s.omega * s.theta) + s.theta ^ 2 =
        (s.omega + s.theta) ^ 2 := by ring
    _ = ((etaZero : 𝓞 K) *
          kappa hζ ^ (587 * s.m - 293) * rhoZero ^ 587) ^ 2 := hsquare
    _ = kappa hζ *
        ((etaZero ^ 2 : (𝓞 K)ˣ) *
          (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2) ^ 587) := by
      simp only [mul_pow, Units.val_pow_eq_pow_val, ← pow_mul]
      rw [hexp, pow_succ']
      ring

set_option maxRecDepth 50000 in
/-- Vandiver's source-faithful real-principal-generator elimination at
exponent 587.  This is the final concrete input required by the historical
well-founded descent. -/
theorem realPrincipalGeneratorElimination587
    {ζ : K} (hζ : IsPrimitiveRoot ζ 587) :
    RealPrincipalGeneratorElimination587 hζ := by
  intro s hs
  obtain ⟨rhoZero, etaZero, jZero, hzero, hgenerator,
      hconjZero, hetaZeroReal⟩ :=
    exists_historicalEquationEightA587 hζ s hs
  obtain ⟨dOne⟩ :=
    exists_preparedEquationEightPair_one587
      hζ s hs rhoZero etaZero hzero
  obtain ⟨dTwo⟩ :=
    exists_preparedEquationEightPair_two587
      hζ s hs rhoZero etaZero hzero
  let D : ℕ := (2 * s.m - 2) * 587
  have hcoefficient :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) * dOne.rplus ^ 587 -
          (dTwo.coefficient : 𝓞 K) * dTwo.rplus ^ 587 := by
    simpa only [D] using
      historicalEquationEight_one_two_coefficients_close587
        hζ s hs dOne.rplus dTwo.rplus
        dOne.coefficient dTwo.coefficient
        dOne.equation_plus dTwo.equation_plus
  have hpowOne :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        dOne.rplus ^ 587 - dOne.mu ^ 344569 := by
    have h := dOne.close_plus.trans
      (sub_dvd_pow_sub_pow dOne.rplus (dOne.mu ^ 587) 587)
    simpa only [D, ← pow_mul] using h
  have hpowTwo :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        dTwo.rplus ^ 587 - dTwo.mu ^ 344569 := by
    have h := dTwo.close_plus.trans
      (sub_dvd_pow_sub_pow dTwo.rplus (dTwo.mu ^ 587) 587)
    simpa only [D, ← pow_mul] using h
  have herrors :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) *
            (dOne.rplus ^ 587 - dOne.mu ^ 344569) -
          (dTwo.coefficient : 𝓞 K) *
            (dTwo.rplus ^ 587 - dTwo.mu ^ 344569) :=
    dvd_sub
      (dvd_mul_of_dvd_right hpowOne (dOne.coefficient : 𝓞 K))
      (dvd_mul_of_dvd_right hpowTwo (dTwo.coefficient : 𝓞 K))
  have hmuD :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) * dOne.mu ^ 344569 -
          (dTwo.coefficient : 𝓞 K) * dTwo.mu ^ 344569 := by
    have h := dvd_sub hcoefficient herrors
    convert h using 1
    ring
  have h1174D : 1174 ≤ D := by
    have hm := s.one_lt_m
    dsimp [D]
    omega
  have hmu1174 :
      ((hζ.unit' : 𝓞 K) - 1) ^ 1174 ∣
        (dOne.coefficient : 𝓞 K) * dOne.mu ^ 344569 -
          (dTwo.coefficient : 𝓞 K) * dTwo.mu ^ 344569 :=
    (pow_dvd_pow ((hζ.unit' : 𝓞 K) - 1) h1174D).trans hmuD
  obtain ⟨c, hratio344569⟩ :=
    exists_int_ratio_pow344569_congruent587 hζ
      dOne.coefficient dTwo.coefficient dOne.mu dTwo.mu
      dOne.mu_real dTwo.mu_real dOne.mu_not_ramified hmu1174
  obtain ⟨rationalBase, hnegativeRatio⟩ :=
    exists_int_negative_square_ratio_pow587_congruent587 hζ
      (dOne.coefficient / dTwo.coefficient) c hratio344569
  let minusOne : (𝓞 K)ˣ := -1
  let epsilonOne : (𝓞 K)ˣ :=
    minusOne *
      (equationTenTraceTwoUnit587 hζ * dOne.coefficient ^ 2)
  let epsilonTwo : (𝓞 K)ˣ :=
    equationTenTraceTwoUnit587 hζ * dTwo.coefficient ^ 2
  let epsilonThree : (𝓞 K)ˣ :=
    minusOne * (equationTenTraceOneUnit587 hζ * etaZero ^ 2)
  have hepsilonRatio :
      epsilonOne / epsilonTwo =
        -((dOne.coefficient / dTwo.coefficient) ^ 2) := by
    have hgroup :
        minusOne *
              (equationTenTraceTwoUnit587 hζ *
                dOne.coefficient ^ 2) /
            (equationTenTraceTwoUnit587 hζ *
              dTwo.coefficient ^ 2) =
          minusOne *
            (dOne.coefficient / dTwo.coefficient) ^ 2 := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        minusOne *
              (equationTenTraceTwoUnit587 hζ *
                dOne.coefficient ^ 2) *
              (dTwo.coefficient⁻¹ ^ 2 *
                (equationTenTraceTwoUnit587 hζ)⁻¹) =
            minusOne *
              (equationTenTraceTwoUnit587 hζ *
                (equationTenTraceTwoUnit587 hζ)⁻¹) *
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
                (equationTenTraceTwoUnit587 hζ *
                  dOne.coefficient ^ 2) /
              (equationTenTraceTwoUnit587 hζ *
                dTwo.coefficient ^ 2) := by
            rfl
      _ = minusOne *
          (dOne.coefficient / dTwo.coefficient) ^ 2 := hgroup
      _ = -((dOne.coefficient / dTwo.coefficient) ^ 2) := by
        dsimp [minusOne]
        ext
        simp
  have hhigh :
      ((1 : 𝓞 K) - hζ.unit') ^ 1174 ∣
        (((epsilonOne / epsilonTwo : (𝓞 K)ˣ) : 𝓞 K) -
          (rationalBase : 𝓞 K) ^ 587) := by
    rw [hepsilonRatio]
    exact hnegativeRatio
  have hquadOne :=
    dOne.quadraticEquation_one hζ s
  have hquadTwo :=
    dTwo.quadraticEquation_two hζ s
  have hquadZero :=
    historicalEquationEightA_quadratic587
      hζ s rhoZero etaZero hzero
  have hweightedRaw :=
    equationTenB_commonKappa587 hζ s.omega s.theta
      (dOne.rplus * dOne.rminus)
      (dTwo.rplus * dTwo.rminus)
      (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2)
      (dOne.coefficient ^ 2)
      (equationTenTraceTwoUnit587 hζ * dTwo.coefficient ^ 2)
      (etaZero ^ 2)
      hquadOne hquadTwo hquadZero
  have hweighted :
      epsilonOne * (dOne.rplus * dOne.rminus) ^ 587 +
          epsilonTwo * (dTwo.rplus * dTwo.rminus) ^ 587 =
        epsilonThree *
          (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2) ^ 587 := by
    dsimp [epsilonOne, epsilonTwo, epsilonThree, minusOne]
    have hweightedRaw' := hweightedRaw
    simp only [Units.val_mul, Units.val_neg,
      Units.val_pow_eq_pow_val] at hweightedRaw'
    linear_combination -hweightedRaw'
  have hrhoZero : rhoZero ≠ 0 := by
    intro hrho
    apply historicalState_omega_add_theta_ne_zero587 hζ s
    rw [hzero, hrho]
    norm_num
  have hcop :=
    equationEight_generators_products_coprime587 hζ
      dOne.coefficient dOne.coefficient
      dTwo.coefficient dTwo.coefficient
      ((etaZero : 𝓞 K) * kappa hζ ^ (587 * s.m - 293))
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
      equationTenTraceOneUnit_real587 hζ, hetaZeroReal]
  have hepsilonTwoReal :
      NumberField.IsCMField.unitsComplexConj K epsilonTwo =
        epsilonTwo := by
    dsimp [epsilonTwo]
    rw [map_mul, map_pow,
      equationTenTraceTwoUnit_real587 hζ, dTwo.coefficient_real]
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
        historicalEquationEightA_square_support_strict_unconditional587
          hζ s hs rhoZero hgenerator }⟩

end

end Fermat.FiveHundredEightySeven.VandiverHistorical

namespace Fermat.FiveHundredEightySeven

open scoped NumberField nonZeroDivisors Cyclotomic

/-- Vandiver's historical proof excludes the second case at exponent 587,
with the cyclotomic field and primitive root chosen canonically. -/
theorem secondCaseExcluded_fiveHundredEightySeven :
    Fermat.SecondCaseExcluded 587 := by
  letI : NeZero (587 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {587} ℚ (CyclotomicField 587 ℚ) :=
    CyclotomicField.isCyclotomicExtension 587 ℚ
  obtain ⟨zeta, hzeta⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 587 ℚ)
      (Set.mem_singleton 587) (by norm_num : 587 ≠ 0)
  intro a b c ha hb hc hgcd hdiv
  exact
    (VandiverHistorical.secondCaseExcluded_587_of_vandiverLemmaTwo
      (K := CyclotomicField 587 ℚ) (ζ := zeta)
      hzeta
      (VandiverHistorical.realPrincipalGeneratorElimination587
        (K := CyclotomicField 587 ℚ) hzeta)
      (VandiverLemmaTwo.vandiverLemmaTwo_fiveHundredEightySeven
        (K := CyclotomicField 587 ℚ)))
      ha hb hc hgcd hdiv

/-- Fermat's Last Theorem at exponent 587. -/
theorem holdsAt_fiveHundredEightySeven : Fermat.HoldsAt 587 := by
  exact Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    (by norm_num) (by norm_num) (by norm_num)
    noConsecutivePowers_587_8219 exponentNotPower_587_8219
    secondCaseExcluded_fiveHundredEightySeven

end Fermat.FiveHundredEightySeven
