import Fermat.OneHundredFiftySeven.VandiverPreparedPair157
import Fermat.OneHundredFiftySeven.VandiverLinearComparison157
import Fermat.OneHundredFiftySeven.VandiverEquationEightAFactorization157
import Fermat.OneHundredFiftySeven.VandiverLemmaTwo
import Fermat.OneHundredFiftySeven.FirstCase
import Fermat.Cases

/-!
# Completion of Vandiver's historical proof at exponent 157

This file assembles the two normalized conjugate equation-(8) pairs, the
local equation-(10) congruence, the three quadratic identities, generator
coprimality, and the strict prime-support descent.  It proves the formerly
isolated `RealPrincipalGeneratorElimination157`, then combines it with the
fully formalized Vandiver Lemma II and Sophie Germain auxiliary prime 1571
to obtain `Fermat.HoldsAt 157`.
-/

namespace Fermat.OneHundredFiftySeven.VandiverHistorical

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverLemmaOne

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {157} ℚ K]

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 157) K (by norm_num)

/-- The first trace unit `A+1` is real, just as the existing second trace
unit `A+2` is. -/
lemma equationTenTraceOneUnit_real157
    {ζ : K} (hζ : IsPrimitiveRoot ζ 157) :
    NumberField.IsCMField.unitsComplexConj K
        (equationTenTraceOneUnit157 hζ) =
      equationTenTraceOneUnit157 hζ := by
  apply Units.ext
  change NumberField.IsCMField.ringOfIntegersComplexConj K
      (equationTenTraceOneUnit157 hζ : 𝓞 K) =
    (equationTenTraceOneUnit157 hζ : 𝓞 K)
  rw [equationTenTraceOneUnit157_val, map_add,
    equationTenTraceOne_real157 hζ, map_one]

omit [NumberField K] [IsCyclotomicExtension {157} ℚ K] in
/-- Squaring historical equation (8a) gives the third quadratic input to
equation (10a). -/
lemma historicalEquationEightA_quadratic157
    {ζ : K} (hζ : IsPrimitiveRoot ζ 157)
    (s : HistoricalState hζ)
    (rhoZero : 𝓞 K) (etaZero : (𝓞 K)ˣ)
    (hzero :
      s.omega + s.theta =
        etaZero * kappa hζ ^ (157 * s.m - 78) * rhoZero ^ 157) :
    s.omega ^ 2 + 2 * (s.omega * s.theta) + s.theta ^ 2 =
      kappa hζ *
        ((etaZero ^ 2 : (𝓞 K)ˣ) *
          (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2) ^ 157) := by
  have hsquare := congrArg (fun x : 𝓞 K ↦ x ^ 2) hzero
  have hexp :
      (157 * s.m - 78) * 2 =
        (2 * s.m - 1) * 157 + 1 := by
    have hm := s.one_lt_m
    omega
  calc
    s.omega ^ 2 + 2 * (s.omega * s.theta) + s.theta ^ 2 =
        (s.omega + s.theta) ^ 2 := by ring
    _ = ((etaZero : 𝓞 K) *
          kappa hζ ^ (157 * s.m - 78) * rhoZero ^ 157) ^ 2 := hsquare
    _ = kappa hζ *
        ((etaZero ^ 2 : (𝓞 K)ˣ) *
          (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2) ^ 157) := by
      simp only [mul_pow, Units.val_pow_eq_pow_val, ← pow_mul]
      rw [hexp, pow_succ']
      ring

set_option maxRecDepth 10000 in
/-- Vandiver's source-faithful real-principal-generator elimination at
exponent 157.  This is the final concrete input required by the historical
well-founded descent. -/
theorem realPrincipalGeneratorElimination157
    {ζ : K} (hζ : IsPrimitiveRoot ζ 157) :
    RealPrincipalGeneratorElimination157 hζ := by
  intro s hs
  obtain ⟨rhoZero, etaZero, jZero, hzero, hgenerator,
      hconjZero, hetaZeroReal⟩ :=
    exists_historicalEquationEightA157 hζ s hs
  obtain ⟨dOne⟩ :=
    exists_preparedEquationEightPair_one157
      hζ s hs rhoZero etaZero hzero
  obtain ⟨dTwo⟩ :=
    exists_preparedEquationEightPair_two157
      hζ s hs rhoZero etaZero hzero
  let D : ℕ := (2 * s.m - 2) * 157
  have hcoefficient :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) * dOne.rplus ^ 157 -
          (dTwo.coefficient : 𝓞 K) * dTwo.rplus ^ 157 := by
    simpa only [D] using
      historicalEquationEight_one_two_coefficients_close157
        hζ s hs dOne.rplus dTwo.rplus
        dOne.coefficient dTwo.coefficient
        dOne.equation_plus dTwo.equation_plus
  have hpowOne :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        dOne.rplus ^ 157 - dOne.mu ^ 24649 := by
    have h := dOne.close_plus.trans
      (sub_dvd_pow_sub_pow dOne.rplus (dOne.mu ^ 157) 157)
    simpa only [D, ← pow_mul] using h
  have hpowTwo :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        dTwo.rplus ^ 157 - dTwo.mu ^ 24649 := by
    have h := dTwo.close_plus.trans
      (sub_dvd_pow_sub_pow dTwo.rplus (dTwo.mu ^ 157) 157)
    simpa only [D, ← pow_mul] using h
  have herrors :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) *
            (dOne.rplus ^ 157 - dOne.mu ^ 24649) -
          (dTwo.coefficient : 𝓞 K) *
            (dTwo.rplus ^ 157 - dTwo.mu ^ 24649) :=
    dvd_sub
      (dvd_mul_of_dvd_right hpowOne (dOne.coefficient : 𝓞 K))
      (dvd_mul_of_dvd_right hpowTwo (dTwo.coefficient : 𝓞 K))
  have hmuD :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) * dOne.mu ^ 24649 -
          (dTwo.coefficient : 𝓞 K) * dTwo.mu ^ 24649 := by
    have h := dvd_sub hcoefficient herrors
    convert h using 1
    ring
  have h314D : 314 ≤ D := by
    have hm := s.one_lt_m
    dsimp [D]
    omega
  have hmu314 :
      ((hζ.unit' : 𝓞 K) - 1) ^ 314 ∣
        (dOne.coefficient : 𝓞 K) * dOne.mu ^ 24649 -
          (dTwo.coefficient : 𝓞 K) * dTwo.mu ^ 24649 :=
    (pow_dvd_pow ((hζ.unit' : 𝓞 K) - 1) h314D).trans hmuD
  obtain ⟨c, hratio24649⟩ :=
    exists_int_ratio_pow24649_congruent157 hζ
      dOne.coefficient dTwo.coefficient dOne.mu dTwo.mu
      dOne.mu_real dTwo.mu_real dOne.mu_not_ramified hmu314
  obtain ⟨rationalBase, hnegativeRatio⟩ :=
    exists_int_negative_square_ratio_pow157_congruent157 hζ
      (dOne.coefficient / dTwo.coefficient) c hratio24649
  let minusOne : (𝓞 K)ˣ := -1
  let epsilonOne : (𝓞 K)ˣ :=
    minusOne *
      (equationTenTraceTwoUnit157 hζ * dOne.coefficient ^ 2)
  let epsilonTwo : (𝓞 K)ˣ :=
    equationTenTraceTwoUnit157 hζ * dTwo.coefficient ^ 2
  let epsilonThree : (𝓞 K)ˣ :=
    minusOne * (equationTenTraceOneUnit157 hζ * etaZero ^ 2)
  have hepsilonRatio :
      epsilonOne / epsilonTwo =
        -((dOne.coefficient / dTwo.coefficient) ^ 2) := by
    have hgroup :
        minusOne *
              (equationTenTraceTwoUnit157 hζ *
                dOne.coefficient ^ 2) /
            (equationTenTraceTwoUnit157 hζ *
              dTwo.coefficient ^ 2) =
          minusOne *
            (dOne.coefficient / dTwo.coefficient) ^ 2 := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        minusOne *
              (equationTenTraceTwoUnit157 hζ *
                dOne.coefficient ^ 2) *
              (dTwo.coefficient⁻¹ ^ 2 *
                (equationTenTraceTwoUnit157 hζ)⁻¹) =
            minusOne *
              (equationTenTraceTwoUnit157 hζ *
                (equationTenTraceTwoUnit157 hζ)⁻¹) *
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
                (equationTenTraceTwoUnit157 hζ *
                  dOne.coefficient ^ 2) /
              (equationTenTraceTwoUnit157 hζ *
                dTwo.coefficient ^ 2) := by
            rfl
      _ = minusOne *
          (dOne.coefficient / dTwo.coefficient) ^ 2 := hgroup
      _ = -((dOne.coefficient / dTwo.coefficient) ^ 2) := by
        dsimp [minusOne]
        ext
        simp
  have hhigh :
      ((1 : 𝓞 K) - hζ.unit') ^ 314 ∣
        (((epsilonOne / epsilonTwo : (𝓞 K)ˣ) : 𝓞 K) -
          (rationalBase : 𝓞 K) ^ 157) := by
    rw [hepsilonRatio]
    exact hnegativeRatio
  have hquadOne :=
    dOne.quadraticEquation_one hζ s
  have hquadTwo :=
    dTwo.quadraticEquation_two hζ s
  have hquadZero :=
    historicalEquationEightA_quadratic157
      hζ s rhoZero etaZero hzero
  have hweightedRaw :=
    equationTenB_commonKappa157 hζ s.omega s.theta
      (dOne.rplus * dOne.rminus)
      (dTwo.rplus * dTwo.rminus)
      (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2)
      (dOne.coefficient ^ 2)
      (equationTenTraceTwoUnit157 hζ * dTwo.coefficient ^ 2)
      (etaZero ^ 2)
      hquadOne hquadTwo hquadZero
  have hweighted :
      epsilonOne * (dOne.rplus * dOne.rminus) ^ 157 +
          epsilonTwo * (dTwo.rplus * dTwo.rminus) ^ 157 =
        epsilonThree *
          (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2) ^ 157 := by
    dsimp [epsilonOne, epsilonTwo, epsilonThree, minusOne]
    have hweightedRaw' := hweightedRaw
    simp only [Units.val_mul, Units.val_neg,
      Units.val_pow_eq_pow_val] at hweightedRaw'
    linear_combination -hweightedRaw'
  have hrhoZero : rhoZero ≠ 0 := by
    intro hrho
    apply historicalState_omega_add_theta_ne_zero157 hζ s
    rw [hzero, hrho]
    norm_num
  have hcop :=
    equationEight_generators_products_coprime157 hζ
      dOne.coefficient dOne.coefficient
      dTwo.coefficient dTwo.coefficient
      ((etaZero : 𝓞 K) * kappa hζ ^ (157 * s.m - 78))
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
      equationTenTraceOneUnit_real157 hζ, hetaZeroReal]
  have hepsilonTwoReal :
      NumberField.IsCMField.unitsComplexConj K epsilonTwo =
        epsilonTwo := by
    dsimp [epsilonTwo]
    rw [map_mul, map_pow,
      equationTenTraceTwoUnit_real157 hζ, dTwo.coefficient_real]
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
        historicalEquationEightA_square_support_strict_unconditional157
          hζ s hs rhoZero hgenerator }⟩

end

end Fermat.OneHundredFiftySeven.VandiverHistorical

namespace Fermat.OneHundredFiftySeven

open scoped NumberField nonZeroDivisors Cyclotomic

/-- Vandiver's historical proof excludes the second case at exponent 157,
with the cyclotomic field and primitive root chosen canonically. -/
theorem secondCaseExcluded_oneHundredFiftySeven :
    Fermat.SecondCaseExcluded 157 := by
  letI : NeZero (157 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {157} ℚ (CyclotomicField 157 ℚ) :=
    CyclotomicField.isCyclotomicExtension 157 ℚ
  obtain ⟨zeta, hzeta⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 157 ℚ)
      (Set.mem_singleton 157) (by norm_num : 157 ≠ 0)
  intro a b c ha hb hc hgcd hdiv
  exact
    (VandiverHistorical.secondCaseExcluded_157_of_vandiverLemmaTwo
      (K := CyclotomicField 157 ℚ) (ζ := zeta)
      hzeta
      (VandiverHistorical.realPrincipalGeneratorElimination157
        (K := CyclotomicField 157 ℚ) hzeta)
      (VandiverLemmaTwo.vandiverLemmaTwo_oneHundredFiftySeven
        (K := CyclotomicField 157 ℚ)))
      ha hb hc hgcd hdiv

/-- Fermat's Last Theorem at exponent 157. -/
theorem holdsAt_oneHundredFiftySeven : Fermat.HoldsAt 157 := by
  exact Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    (by norm_num) (by norm_num) (by norm_num)
    noConsecutivePowers_157_1571 exponentNotPower_157_1571
    secondCaseExcluded_oneHundredFiftySeven

end Fermat.OneHundredFiftySeven
