import Fermat.Irregular.TakagiHistoricalPrime
import Fermat.Irregular.VandiverPreparedPairPrime
import Fermat.Irregular.VandiverLinearComparisonPrime
import Fermat.Irregular.VandiverHistoricalQuadraticPrime
import Fermat.Irregular.VandiverCongruenceSupportPrime
import Fermat.Irregular.VandiverGeneratorSupportPrime
import Fermat.Irregular.VandiverEquationEightAFactorizationPrime
import Fermat.Irregular.VandiverEquationTenPrime

set_option maxRecDepth 50000

/-!
# Prime-generic assembly of Vandiver's historical elimination

This module joins the generic equation-(8a), the two prepared conjugate
equation-(8) pairs, equations (9)--(10), and the strict factor-support
drop.  For every prime `p ≥ 5`, the only exponent-specific input is the
checked plus-class nondivisibility

`p ∤ h(K⁺)`.

All remaining work is algebraic and is performed here once for every
prime.  Bernoulli data, Vandiver's Lemma II, and an auxiliary prime do not
enter this construction.
-/

open scoped NumberField nonZeroDivisors

namespace Fermat.Irregular.VandiverHistoricalAssemblyPrime

noncomputable section

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime
open Fermat.Irregular.VandiverHistoricalStatePrime
open Fermat.Irregular.VandiverHistoricalEquationEightAPrime
open Fermat.Irregular.TakagiHistoricalPrime
open Fermat.Irregular.VandiverPreparedPairPrime
open Fermat.Irregular.VandiverLinearComparisonPrime
open Fermat.Irregular.VandiverHistoricalQuadraticPrime
open Fermat.Irregular.VandiverCongruenceSupportPrime
open Fermat.Irregular.VandiverGeneratorSupportPrime
open Fermat.Irregular.VandiverEquationEightAFactorizationPrime
open Fermat.Irregular.VandiverEquationTenPrime

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

set_option maxRecDepth 50000 in
/-- The complete prime-generic real-principal-generator elimination.

The plus-class certificate is used both by Takagi reflection for the
conjugate equation-(8) pairs and by the real generator extractions in
equations (8a) and (9). -/
theorem realPrincipalGeneratorElimination_of_plusClass
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hplus : PlusClassNondivisibility K p) :
    RealPrincipalGeneratorElimination hζ := by
  have hp2 : p ≠ 2 := by omega
  have hcop2 : Nat.Coprime 2 p :=
    coprime_two_prime hp5
  obtain ⟨r, hr⟩ :=
    (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  intro s hs
  obtain ⟨rhoZero, etaZero, jZero, hzero, hgenerator,
      hconjZero, hetaZeroReal⟩ :=
    exists_historicalEquationEightA
      hplus hp5 hcop2 hr hζ s hs
  obtain ⟨dOne⟩ :=
    exists_historicalPreparedEquationEightPair_one_of_plusClass
      hplus hp5 hcop2 hr hζ s hs rhoZero etaZero hzero
  obtain ⟨dTwo⟩ :=
    exists_historicalPreparedEquationEightPair_two_of_plusClass
      hplus hp5 hcop2 hr hζ s hs rhoZero etaZero hzero
  let D : ℕ := (2 * s.m - 2) * p
  have hsourceDepth :
      ((hζ.unit' : 𝓞 K) - 1) ^ (D + 1) ∣
        s.omega + s.theta := by
    have hfull :=
      historicalState_omega_add_theta_fullHighDivisibility
        hp2 hζ s hs
    have hle :
        D + 1 ≤ (2 * s.m - 1) * p + 1 := by
      have hm := s.one_lt_m
      have hcoefficient :
          2 * s.m - 2 ≤ 2 * s.m - 1 := by
        omega
      dsimp [D]
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_right p hcoefficient) 1
    exact
      (pow_dvd_pow ((hζ.unit' : 𝓞 K) - 1) hle).trans
        hfull
  have hcoefficient :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) * dOne.rplus ^ p -
          (dTwo.coefficient : 𝓞 K) * dTwo.rplus ^ p := by
    exact
      equationEight_one_two_coefficients_close
        hcop2 hζ D s.omega s.theta
        dOne.rplus dTwo.rplus
        dOne.coefficient dTwo.coefficient
        hsourceDepth dOne.equation_plus dTwo.equation_plus
  have hpowOne :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        dOne.rplus ^ p - dOne.mu ^ (p ^ 2) := by
    have h := dOne.close_plus.trans
      (sub_dvd_pow_sub_pow dOne.rplus (dOne.mu ^ p) p)
    simpa only [D, ← pow_mul, pow_two] using h
  have hpowTwo :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        dTwo.rplus ^ p - dTwo.mu ^ (p ^ 2) := by
    have h := dTwo.close_plus.trans
      (sub_dvd_pow_sub_pow dTwo.rplus (dTwo.mu ^ p) p)
    simpa only [D, ← pow_mul, pow_two] using h
  have herrors :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) *
            (dOne.rplus ^ p - dOne.mu ^ (p ^ 2)) -
          (dTwo.coefficient : 𝓞 K) *
            (dTwo.rplus ^ p - dTwo.mu ^ (p ^ 2)) :=
    dvd_sub
      (dvd_mul_of_dvd_right hpowOne
        (dOne.coefficient : 𝓞 K))
      (dvd_mul_of_dvd_right hpowTwo
        (dTwo.coefficient : 𝓞 K))
  have hmuD :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) * dOne.mu ^ (p ^ 2) -
          (dTwo.coefficient : 𝓞 K) * dTwo.mu ^ (p ^ 2) := by
    have h := dvd_sub hcoefficient herrors
    convert h using 1
    ring
  have htwoPD : 2 * p ≤ D := by
    have hm := s.one_lt_m
    have hcoefficient : 2 ≤ 2 * s.m - 2 := by
      omega
    dsimp [D]
    exact Nat.mul_le_mul_right p hcoefficient
  have hmuTwoP :
      ((hζ.unit' : 𝓞 K) - 1) ^ (2 * p) ∣
        (dOne.coefficient : 𝓞 K) * dOne.mu ^ (p ^ 2) -
          (dTwo.coefficient : 𝓞 K) * dTwo.mu ^ (p ^ 2) :=
    (pow_dvd_pow ((hζ.unit' : 𝓞 K) - 1) htwoPD).trans
      hmuD
  obtain ⟨c, hratioPSq⟩ :=
    exists_int_ratio_pow_sq_congruent hp2 hζ
      dOne.coefficient dTwo.coefficient dOne.mu dTwo.mu
      dOne.mu_real dTwo.mu_real dOne.mu_not_ramified
      hmuTwoP
  obtain ⟨rationalBase, hnegativeRatio⟩ :=
    exists_int_negative_square_ratio_pow_congruent hp2 hζ
      (dOne.coefficient / dTwo.coefficient) c hratioPSq
  let minusOne : (𝓞 K)ˣ := -1
  let epsilonOne : (𝓞 K)ˣ :=
    minusOne *
      (equationTenTraceTwoUnit hp5 hζ *
        dOne.coefficient ^ 2)
  let epsilonTwo : (𝓞 K)ˣ :=
    equationTenTraceTwoUnit hp5 hζ *
      dTwo.coefficient ^ 2
  let epsilonThree : (𝓞 K)ˣ :=
    minusOne *
      (equationTenTraceOneUnit hp5 hζ * etaZero ^ 2)
  have hepsilonRatio :
      epsilonOne / epsilonTwo =
        -((dOne.coefficient / dTwo.coefficient) ^ 2) := by
    have hgroup :
        minusOne *
              (equationTenTraceTwoUnit hp5 hζ *
                dOne.coefficient ^ 2) /
            (equationTenTraceTwoUnit hp5 hζ *
              dTwo.coefficient ^ 2) =
          minusOne *
            (dOne.coefficient / dTwo.coefficient) ^ 2 := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        minusOne *
              (equationTenTraceTwoUnit hp5 hζ *
                dOne.coefficient ^ 2) *
              (dTwo.coefficient⁻¹ ^ 2 *
                (equationTenTraceTwoUnit hp5 hζ)⁻¹) =
            minusOne *
              (equationTenTraceTwoUnit hp5 hζ *
                (equationTenTraceTwoUnit hp5 hζ)⁻¹) *
              (dOne.coefficient ^ 2 *
                dTwo.coefficient⁻¹ ^ 2) := by
          ac_rfl
        _ =
            minusOne *
              (dOne.coefficient ^ 2 *
                dTwo.coefficient⁻¹ ^ 2) := by simp
        _ =
            minusOne *
              (dOne.coefficient * dTwo.coefficient⁻¹) ^ 2 := by
          rw [mul_pow]
    calc
      epsilonOne / epsilonTwo =
          minusOne *
                (equationTenTraceTwoUnit hp5 hζ *
                  dOne.coefficient ^ 2) /
              (equationTenTraceTwoUnit hp5 hζ *
                dTwo.coefficient ^ 2) := by
            rfl
      _ =
          minusOne *
            (dOne.coefficient / dTwo.coefficient) ^ 2 :=
        hgroup
      _ =
          -((dOne.coefficient / dTwo.coefficient) ^ 2) := by
        dsimp [minusOne]
        ext
        simp
  have hhigh :
      ((1 : 𝓞 K) - hζ.unit') ^ (2 * p) ∣
        (((epsilonOne / epsilonTwo : (𝓞 K)ˣ) : 𝓞 K) -
          (rationalBase : 𝓞 K) ^ p) := by
    rw [hepsilonRatio]
    exact hnegativeRatio
  have hquadOne :=
    dOne.quadraticEquation_one hζ s
  have hquadTwo :=
    dTwo.quadraticEquation_two hζ s hp5
  have hquadZero :=
    historicalEquationEightA_quadratic
      hr hζ s.m s.one_lt_m
      s.omega s.theta rhoZero etaZero hzero
  have hweightedRaw :=
    equationTenB_commonKappa hp5 hζ
      s.omega s.theta
      (dOne.rplus * dOne.rminus)
      (dTwo.rplus * dTwo.rminus)
      (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2)
      (dOne.coefficient ^ 2)
      (equationTenTraceTwoUnit hp5 hζ *
        dTwo.coefficient ^ 2)
      (etaZero ^ 2)
      hquadOne hquadTwo hquadZero
  have hweighted :
      epsilonOne * (dOne.rplus * dOne.rminus) ^ p +
          epsilonTwo * (dTwo.rplus * dTwo.rminus) ^ p =
        epsilonThree *
          (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2) ^ p := by
    dsimp [epsilonOne, epsilonTwo, epsilonThree, minusOne]
    have hweightedRaw' := hweightedRaw
    simp only [Units.val_mul, Units.val_neg,
      Units.val_pow_eq_pow_val] at hweightedRaw'
    linear_combination -hweightedRaw'
  have hrhoZero : rhoZero ≠ 0 := by
    intro hrho
    apply historicalState_omega_add_theta_ne_zero hp2 hζ s
    rw [hzero, hrho]
    simp only [zero_pow (Fact.out : Nat.Prime p).ne_zero,
      mul_zero]
  have hcop :=
    equationEight_generators_products_coprime hp5 hζ
      dOne.coefficient dOne.coefficient
      dTwo.coefficient dTwo.coefficient
      ((etaZero : 𝓞 K) * kappa hζ ^ (p * s.m - r))
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
    change
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (-1 : 𝓞 K) =
        -1
    rw [map_neg, map_one]
  have hepsilonThreeReal :
      NumberField.IsCMField.unitsComplexConj K epsilonThree =
        epsilonThree := by
    dsimp [epsilonThree]
    rw [map_mul, hminusOneReal, map_mul,
      equationTenTraceOneUnit_real hp5 hζ, hetaZeroReal]
  have hepsilonTwoReal :
      NumberField.IsCMField.unitsComplexConj K epsilonTwo =
        epsilonTwo := by
    dsimp [epsilonTwo]
    rw [map_mul, map_pow,
      equationTenTraceTwoUnit_real hp5 hζ,
      dTwo.coefficient_real]
  have hrealEta :
      NumberField.IsCMField.unitsComplexConj K
          (epsilonThree / epsilonTwo) =
        epsilonThree / epsilonTwo := by
    rw [map_div, hepsilonThreeReal, hepsilonTwoReal]
  exact
    ⟨{ x := dOne.rplus * dOne.rminus
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
         simpa using
           dTwo.product_real hζ s (hζ.unit' ^ 2)
       conjugation_z := hconjZero
       real_eta := hrealEta
       factorSupport_strict :=
         historicalEquationEightA_square_support_strict_unconditional
           hp5 hζ s hs rhoZero hgenerator }⟩

end

end Fermat.Irregular.VandiverHistoricalAssemblyPrime
