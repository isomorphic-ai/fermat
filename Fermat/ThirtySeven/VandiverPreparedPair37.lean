import Fermat.ThirtySeven.TakagiHistorical37
import Fermat.ThirtySeven.VandiverPostNineGenerator37
import Fermat.ThirtySeven.VandiverGeneratorSupport37

/-!
# Prepared conjugate equation-(8) pairs at exponent 37

This module packages the source-faithful transition from Vandiver's paired
equations (8) through the normalized equation (9a).  It extracts the real
principal generator of the fixed-denominator quotient, proves that its
residual unit is real, absorbs that unit into both roots, and exposes the
quadratic identities used in equation (10).
-/

namespace Fermat.ThirtySeven.VandiverHistorical

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverLemmaOne

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 37) K (by norm_num)

/-- A normalized conjugate pair after Vandiver's equation (9), with the
quotient unit absorbed into both roots. -/
structure PreparedEquationEightPair37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (s : HistoricalState hζ) (t : (𝓞 K)ˣ) where
  rplus : 𝓞 K
  rminus : 𝓞 K
  mu : 𝓞 K
  coefficient : (𝓞 K)ˣ
  coefficient_real :
    NumberField.IsCMField.unitsComplexConj K coefficient = coefficient
  equation_plus :
    s.omega + (t : 𝓞 K) * s.theta =
      (1 - (t : 𝓞 K)) * coefficient * rplus ^ 37
  equation_minus :
    s.omega + (t⁻¹ : (𝓞 K)ˣ) * s.theta =
      (1 - (t⁻¹ : (𝓞 K)ˣ)) * coefficient * rminus ^ 37
  conjugate :
    NumberField.IsCMField.ringOfIntegersComplexConj K rplus = rminus
  rplus_not_ramified :
    ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rplus
  rminus_not_ramified :
    ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rminus
  mu_real :
    NumberField.IsCMField.ringOfIntegersComplexConj K mu = mu
  mu_not_ramified :
    ¬ (hζ.unit' : 𝓞 K) - 1 ∣ mu
  close_plus :
    ((hζ.unit' : 𝓞 K) - 1) ^ ((2 * s.m - 2) * 37) ∣
      rplus - mu ^ 37
  close_minus :
    ((hζ.unit' : 𝓞 K) - 1) ^ ((2 * s.m - 2) * 37) ∣
      rminus - mu ^ 37

namespace PreparedEquationEightPair37

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
  (s : HistoricalState hζ) (t : (𝓞 K)ˣ)
  (d : PreparedEquationEightPair37 hζ s t)

/-- Multiplying the two rescaled conjugate linear equations gives the
quadratic equation used in Vandiver's equation (10). -/
lemma quadraticEquation :
    s.omega ^ 2 +
        ((t : 𝓞 K) + (t⁻¹ : (𝓞 K)ˣ)) *
          (s.omega * s.theta) +
        s.theta ^ 2 =
      ((1 - (t : 𝓞 K)) * (1 - (t⁻¹ : (𝓞 K)ˣ))) *
        ((d.coefficient ^ 2 : (𝓞 K)ˣ) *
          (d.rplus * d.rminus) ^ 37) := by
  have htinv :
      (t : 𝓞 K) * (t⁻¹ : (𝓞 K)ˣ) = 1 := by
    rw [← Units.val_mul]
    simp
  calc
    s.omega ^ 2 +
          ((t : 𝓞 K) + (t⁻¹ : (𝓞 K)ˣ)) *
            (s.omega * s.theta) +
          s.theta ^ 2 =
        (s.omega + (t : 𝓞 K) * s.theta) *
          (s.omega + (t⁻¹ : (𝓞 K)ˣ) * s.theta) := by
      linear_combination -(s.theta ^ 2) * htinv
    _ = ((1 - (t : 𝓞 K)) * d.coefficient * d.rplus ^ 37) *
        ((1 - (t⁻¹ : (𝓞 K)ˣ)) * d.coefficient *
          d.rminus ^ 37) := by
      rw [d.equation_plus, d.equation_minus]
    _ = ((1 - (t : 𝓞 K)) * (1 - (t⁻¹ : (𝓞 K)ˣ))) *
        ((d.coefficient ^ 2 : (𝓞 K)ˣ) *
          (d.rplus * d.rminus) ^ 37) := by
      simp only [Units.val_pow_eq_pow_val, mul_pow]
      ring

/-- The product of the two prepared conjugate roots is literally real. -/
lemma product_real :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (d.rplus * d.rminus) =
      d.rplus * d.rminus := by
  have hminus :
      NumberField.IsCMField.ringOfIntegersComplexConj K d.rminus =
        d.rplus := by
    have hcc := congrArg
      (NumberField.IsCMField.ringOfIntegersComplexConj K) d.conjugate
    have hinvol :
        NumberField.IsCMField.ringOfIntegersComplexConj K
            (NumberField.IsCMField.ringOfIntegersComplexConj K d.rplus) =
          d.rplus := by
      apply NumberField.RingOfIntegers.ext
      exact NumberField.IsCMField.complexConj_apply_apply K d.rplus
    simpa only [hinvol] using hcc.symm
  rw [map_mul, d.conjugate, hminus, mul_comm]

/-- Quadratic equation (10) for the prepared pair at `1,-1`. -/
lemma quadraticEquation_one
    (d : PreparedEquationEightPair37 hζ s hζ.unit') :
    s.omega ^ 2 +
        equationTenTraceOne37 hζ * (s.omega * s.theta) +
        s.theta ^ 2 =
      kappa hζ *
        ((d.coefficient ^ 2 : (𝓞 K)ˣ) *
          (d.rplus * d.rminus) ^ 37) := by
  simpa only [equationTenTraceOne37, kappa] using
    d.quadraticEquation hζ s hζ.unit'

/-- Quadratic equation (10) for the prepared pair at `2,-2`. -/
lemma quadraticEquation_two
    (d : PreparedEquationEightPair37 hζ s (hζ.unit' ^ 2)) :
    s.omega ^ 2 +
        equationTenTraceTwo37 hζ * (s.omega * s.theta) +
        s.theta ^ 2 =
      kappa hζ *
        ((equationTenTraceTwoUnit37 hζ * d.coefficient ^ 2 :
            (𝓞 K)ˣ) *
          (d.rplus * d.rminus) ^ 37) := by
  have htrace :
      (((hζ.unit' ^ 2 : (𝓞 K)ˣ) : 𝓞 K) +
          (((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) =
        equationTenTraceTwo37 hζ := by
    simp only [equationTenTraceTwo37, Units.val_pow_eq_pow_val]
    congr 1
  have hden :
      (1 - ((hζ.unit' ^ 2 : (𝓞 K)ˣ) : 𝓞 K)) *
          (1 - (((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) =
        kappa hζ * (equationTenTraceTwoUnit37 hζ : 𝓞 K) := by
    calc
      _ = kappa (hζ.pow_of_coprime 2 (by norm_num)) := by
        simp only [kappa, powTwoPrimitiveRoot_unit37 hζ]
      _ = _ := kappa_powTwoPrimitiveRoot37 hζ
  have hq := d.quadraticEquation hζ s (hζ.unit' ^ 2)
  rw [htrace, hden] at hq
  calc
    s.omega ^ 2 +
          equationTenTraceTwo37 hζ * (s.omega * s.theta) +
          s.theta ^ 2 =
        (kappa hζ * (equationTenTraceTwoUnit37 hζ : 𝓞 K)) *
          ((d.coefficient ^ 2 : (𝓞 K)ˣ) *
            (d.rplus * d.rminus) ^ 37) := hq
    _ = kappa hζ *
        ((equationTenTraceTwoUnit37 hζ * d.coefficient ^ 2 :
            (𝓞 K)ˣ) *
          (d.rplus * d.rminus) ^ 37) := by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      ring

end PreparedEquationEightPair37

namespace PostEquationNineNormalizedData37

/-- Since both Vandiver's fixed-denominator quotient and its chosen
generator are real, the residual unit in `q = η μ^37` is real as well. -/
lemma generator_unit_real
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (d : PostEquationNineNormalizedData37 hζ)
    (μ : 𝓞 K) (η : (𝓞 K)ˣ)
    (hμreal :
      NumberField.IsCMField.ringOfIntegersComplexConj K μ = μ)
    (hμnot : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ μ)
    (hq : quotient hζ d = η * μ ^ 37) :
    NumberField.IsCMField.unitsComplexConj K η = η := by
  have hμ0 : μ ≠ 0 := by
    intro hμ
    subst μ
    exact hμnot (dvd_zero _)
  apply Units.ext
  change
    NumberField.IsCMField.ringOfIntegersComplexConj K (η : 𝓞 K) =
      (η : 𝓞 K)
  apply mul_right_cancel₀ (pow_ne_zero 37 hμ0)
  have hqreal := d.quotient_real hζ
  calc
    (NumberField.IsCMField.unitsComplexConj K η : 𝓞 K) * μ ^ 37 =
        NumberField.IsCMField.ringOfIntegersComplexConj K
          ((η : 𝓞 K) * μ ^ 37) := by
      rw [map_mul, map_pow, hμreal]
      change
        NumberField.IsCMField.ringOfIntegersComplexConj K (η : 𝓞 K) *
            μ ^ 37 =
          NumberField.IsCMField.ringOfIntegersComplexConj K (η : 𝓞 K) *
            μ ^ 37
      rfl
    _ = NumberField.IsCMField.ringOfIntegersComplexConj K
          (quotient hζ d) := by rw [hq]
    _ = quotient hζ d := hqreal
    _ = (η : 𝓞 K) * μ ^ 37 := hq

end PostEquationNineNormalizedData37

set_option maxRecDepth 4000 in
/-- Generic preparation of a conjugate equation-(8) pair.  It carries out
the difference equation, symmetric equation-(9a) normalization, real
principal-generator extraction, and absorption of the resulting real
unit. -/
theorem exists_preparedEquationEightPair37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (s : HistoricalState hζ)
    (a : ℕ) (ha : a.Coprime 37)
    (rhoPlus rhoMinus rhoZero : 𝓞 K)
    (eta etaZero : (𝓞 K)ˣ)
    (hetaReal :
      NumberField.IsCMField.unitsComplexConj K eta = eta)
    (hplus :
      s.omega + (hζ.unit' ^ a : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit' ^ a : (𝓞 K)ˣ)) * eta * rhoPlus ^ 37)
    (hminus :
      s.omega + ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ) * s.theta =
        (1 - ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ)) * eta *
          rhoMinus ^ 37)
    (hzero :
      s.omega + s.theta =
        etaZero * kappa hζ ^ (37 * s.m - 18) * rhoZero ^ 37)
    (hconj :
      NumberField.IsCMField.ringOfIntegersComplexConj K rhoPlus =
        rhoMinus)
    (hpair : IsCoprime rhoPlus rhoMinus)
    (hminusNot :
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rhoMinus) :
    Nonempty
      (PreparedEquationEightPair37 hζ s (hζ.unit' ^ a)) := by
  classical
  obtain ⟨epsilon, hdifference⟩ :=
    exists_equationEight_difference37 hζ a s.m ha s.one_lt_m
      s.omega s.theta rhoPlus rhoMinus rhoZero eta etaZero
      hplus hminus hzero
  obtain ⟨nplus, nminus, hnplus, hnminus, hclose,
      hnconj, hnminusNot⟩ :=
    equationNineA_normalized_conjugate37 hζ s.m s.one_lt_m
      rhoPlus rhoMinus rhoZero epsilon hdifference hconj hminusNot
  have hnpair : IsCoprime nplus nminus := by
    have hpowers : IsCoprime (nplus ^ 37) (nminus ^ 37) := by
      rw [hnplus, hnminus]
      exact hpair.pow_left.pow_right
    exact
      (IsCoprime.pow_left_iff (by norm_num : 0 < 37)).mp
        ((IsCoprime.pow_right_iff (by norm_num : 0 < 37)).mp hpowers)
  let D : ℕ := (2 * s.m - 2) * 37
  let post : PostEquationNineNormalizedData37 hζ :=
    { m := s.m
      one_lt_m := s.one_lt_m
      rplus := nplus
      rminus := nminus
      rzero := rhoZero
      epsilon := epsilon
      equation := by
        rw [hnplus, hnminus]
        exact hdifference
      conjugate := hnconj
      coprime := hnpair
      rminus_not_ramified := hnminusNot
      depth := D + 1
      two_le_depth := by
        have hm := s.one_lt_m
        dsimp [D]
        omega
      close := by
        simpa only [D] using hclose }
  obtain ⟨mu, delta, -, hmureal, hquotient, hmuNot,
      hminusQ, hplusQ⟩ :=
    post.exists_real_generator hζ
  have hdeltaReal :
      NumberField.IsCMField.unitsComplexConj K delta = delta :=
    post.generator_unit_real hζ mu delta hmureal hmuNot hquotient
  let rplus : 𝓞 K := (delta⁻¹ : (𝓞 K)ˣ) * nplus
  let rminus : 𝓞 K := (delta⁻¹ : (𝓞 K)ˣ) * nminus
  let coefficient : (𝓞 K)ˣ := eta * delta ^ 37
  have hcoefficientReal :
      NumberField.IsCMField.unitsComplexConj K coefficient =
        coefficient := by
    dsimp [coefficient]
    rw [map_mul, map_pow, hetaReal, hdeltaReal]
  have hdeltaCancel :
      (delta : 𝓞 K) ^ 37 *
          ((delta⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ 37 = 1 := by
    rw [← mul_pow, ← Units.val_mul]
    simp
  have hequationPlus :
      s.omega + (hζ.unit' ^ a : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit' ^ a : (𝓞 K)ˣ)) *
          coefficient * rplus ^ 37 := by
    have hscaled :
        (coefficient : 𝓞 K) * rplus ^ 37 =
          (eta : 𝓞 K) * rhoPlus ^ 37 := by
      dsimp [coefficient, rplus]
      simp only [mul_pow]
      rw [hnplus]
      calc
        ((eta : 𝓞 K) * (delta : 𝓞 K) ^ 37) *
            (((delta⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ 37 *
              rhoPlus ^ 37) =
          (eta : 𝓞 K) *
            (((delta : 𝓞 K) ^ 37 *
              ((delta⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ 37) *
                rhoPlus ^ 37) := by ac_rfl
        _ = (eta : 𝓞 K) * rhoPlus ^ 37 := by
          rw [hdeltaCancel, one_mul]
    calc
      s.omega + (hζ.unit' ^ a : (𝓞 K)ˣ) * s.theta =
          (1 - (hζ.unit' ^ a : (𝓞 K)ˣ)) *
            ((eta : 𝓞 K) * rhoPlus ^ 37) := by
        simpa only [mul_assoc] using hplus
      _ = (1 - (hζ.unit' ^ a : (𝓞 K)ˣ)) *
          ((coefficient : 𝓞 K) * rplus ^ 37) := by
        rw [hscaled]
      _ = _ := by rw [mul_assoc]
  have hequationMinus :
      s.omega + ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ) * s.theta =
        (1 - ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ)) *
          coefficient * rminus ^ 37 := by
    have hscaled :
        (coefficient : 𝓞 K) * rminus ^ 37 =
          (eta : 𝓞 K) * rhoMinus ^ 37 := by
      dsimp [coefficient, rminus]
      simp only [mul_pow]
      rw [hnminus]
      calc
        ((eta : 𝓞 K) * (delta : 𝓞 K) ^ 37) *
            (((delta⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ 37 *
              rhoMinus ^ 37) =
          (eta : 𝓞 K) *
            (((delta : 𝓞 K) ^ 37 *
              ((delta⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ 37) *
                rhoMinus ^ 37) := by ac_rfl
        _ = (eta : 𝓞 K) * rhoMinus ^ 37 := by
          rw [hdeltaCancel, one_mul]
    calc
      s.omega + ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ) * s.theta =
          (1 - ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ)) *
            ((eta : 𝓞 K) * rhoMinus ^ 37) := by
        simpa only [mul_assoc] using hminus
      _ = (1 - ((hζ.unit' ^ a)⁻¹ : (𝓞 K)ˣ)) *
          ((coefficient : 𝓞 K) * rminus ^ 37) := by
        rw [hscaled]
      _ = _ := by rw [mul_assoc]
  have hconjugate :
      NumberField.IsCMField.ringOfIntegersComplexConj K rplus =
        rminus := by
    have hdeltaInvReal :
        NumberField.IsCMField.unitsComplexConj K delta⁻¹ = delta⁻¹ := by
      rw [map_inv, hdeltaReal]
    dsimp [rplus, rminus]
    rw [map_mul, hnconj]
    exact congrArg (fun u : (𝓞 K)ˣ ↦
      (u : 𝓞 K) * nminus) hdeltaInvReal
  have hrplusNot :
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rplus := by
    intro h
    have hn : (hζ.unit' : 𝓞 K) - 1 ∣ nplus := by
      have hscaled := dvd_mul_of_dvd_right h (delta : 𝓞 K)
      convert hscaled using 1
      dsimp [rplus]
      rw [← mul_assoc, ← Units.val_mul]
      simp
    have hc := zeta_sub_one_pow_dvd_conj_of_dvd37 hζ 1 nplus
      (by simpa only [pow_one] using hn)
    apply hnminusNot
    simpa only [pow_one, hnconj] using hc
  have hrminusNot :
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rminus := by
    intro h
    apply hnminusNot
    have hscaled := dvd_mul_of_dvd_right h (delta : 𝓞 K)
    convert hscaled using 1
    dsimp [rminus]
    rw [← mul_assoc, ← Units.val_mul]
    simp
  have hcloseMinus :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        rminus - mu ^ 37 := by
    simpa only [post, D, Nat.add_sub_cancel, rminus] using
      post.pow_pred_dvd_inv_unit_mul_rminus_sub_pow hζ
        mu delta hquotient
  have hclosePlus :
      ((hζ.unit' : 𝓞 K) - 1) ^ D ∣
        rplus - mu ^ 37 := by
    simpa only [post, D, Nat.add_sub_cancel, rplus] using
      post.pow_pred_dvd_inv_unit_mul_rplus_sub_pow hζ
        mu delta hplusQ
  exact ⟨
    { rplus := rplus
      rminus := rminus
      mu := mu
      coefficient := coefficient
      coefficient_real := hcoefficientReal
      equation_plus := hequationPlus
      equation_minus := hequationMinus
      conjugate := hconjugate
      rplus_not_ramified := hrplusNot
      rminus_not_ramified := hrminusNot
      mu_real := hmureal
      mu_not_ramified := hmuNot
      close_plus := by simpa only [D] using hclosePlus
      close_minus := by simpa only [D] using hcloseMinus }⟩

/-- The two generators in the historical pair at `1,-1` are coprime. -/
theorem equationEight_pair_one_generators_coprime37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (s : HistoricalState hζ)
    (rhoPlus rhoMinus : 𝓞 K) (eta : (𝓞 K)ˣ)
    (hplus :
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
        (1 - (hζ.unit' : 𝓞 K)) * eta * rhoPlus ^ 37)
    (hminus :
      s.omega + (hζ.unit'⁻¹ : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit'⁻¹ : (𝓞 K)ˣ)) * eta *
          rhoMinus ^ 37) :
    IsCoprime rhoPlus rhoMinus := by
  let pi : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  have hpi0 : pi ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero (by norm_num)
  have hcPlus :
      Associated
        ((1 - (hζ.unit' : 𝓞 K)) * (eta : 𝓞 K)) pi := by
    simpa only [pi, pow_one] using
      associated_one_sub_zetaPow_mul_unit37 hζ 1
        (by norm_num) (by norm_num) eta
  have hcMinus :
      Associated
        ((1 - (hζ.unit'⁻¹ : (𝓞 K)ˣ)) * (eta : 𝓞 K)) pi := by
    rw [zetaUnit_inv_eq_pow_thirtySix37 hζ]
    simpa only [pi, Units.val_pow_eq_pow_val] using
      associated_one_sub_zetaPow_mul_unit37 hζ 36
        (by norm_num) (by norm_num) eta
  have ht :
      Associated
        ((hζ.unit' : 𝓞 K) - (hζ.unit'⁻¹ : (𝓞 K)ˣ)) pi := by
    rw [zetaUnit_inv_eq_pow_thirtySix37 hζ]
    simpa only [pi, pow_one, Units.val_pow_eq_pow_val] using
      associated_zetaPowers_sub37 hζ
        (a := 1) (b := 36)
        (by norm_num) (by norm_num) (by norm_num)
  exact coprime_generators_of_distinct_linearEquations37
    hpi0 s.coprime_omega_theta hcPlus hcMinus ht
    (by simpa only [mul_assoc] using hplus)
    (by simpa only [mul_assoc] using hminus)

/-- The two generators in the historical pair at `2,-2` are coprime. -/
theorem equationEight_pair_two_generators_coprime37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (s : HistoricalState hζ)
    (rhoPlus rhoMinus : 𝓞 K) (eta : (𝓞 K)ˣ)
    (hplus :
      s.omega + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * eta * rhoPlus ^ 37)
    (hminus :
      s.omega + ((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ) * s.theta =
        (1 - ((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ)) * eta *
          rhoMinus ^ 37) :
    IsCoprime rhoPlus rhoMinus := by
  let pi : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  have hpi0 : pi ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero (by norm_num)
  have hcPlus :
      Associated
        ((1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * (eta : 𝓞 K)) pi := by
    simpa only [pi, Units.val_pow_eq_pow_val] using
      associated_one_sub_zetaPow_mul_unit37 hζ 2
        (by norm_num) (by norm_num) eta
  have hcMinus :
      Associated
        ((1 - ((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ)) *
          (eta : 𝓞 K)) pi := by
    rw [zetaUnit_sq_inv_eq_pow_thirtyFive37 hζ]
    simpa only [pi, Units.val_pow_eq_pow_val] using
      associated_one_sub_zetaPow_mul_unit37 hζ 35
        (by norm_num) (by norm_num) eta
  have ht :
      Associated
        (((hζ.unit' ^ 2 : (𝓞 K)ˣ) : 𝓞 K) -
          (((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) pi := by
    rw [zetaUnit_sq_inv_eq_pow_thirtyFive37 hζ]
    simpa only [pi, Units.val_pow_eq_pow_val] using
      associated_zetaPowers_sub37 hζ
        (a := 2) (b := 35)
        (by norm_num) (by norm_num) (by norm_num)
  exact coprime_generators_of_distinct_linearEquations37
    hpi0 s.coprime_omega_theta hcPlus hcMinus ht
    (by simpa only [mul_assoc] using hplus)
    (by simpa only [mul_assoc] using hminus)

/-- Fully prepared historical pair at `1,-1`, with the unconditional
Takagi--Furtwängler input already discharged. -/
theorem exists_preparedEquationEightPair_one37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (s : HistoricalState hζ) (hs : RealSourceAdmissible hζ s)
    (rhoZero : 𝓞 K) (etaZero : (𝓞 K)ˣ)
    (hzero :
      s.omega + s.theta =
        etaZero * kappa hζ ^ (37 * s.m - 18) * rhoZero ^ 37) :
    Nonempty (PreparedEquationEightPair37 hζ s hζ.unit') := by
  obtain ⟨rhoPlus, rhoMinus, eta, hetaReal, hplus, hminus,
      hconj, -, hminusNot⟩ :=
    _root_.Fermat.ThirtySeven.TakagiHistorical37.exists_historicalEquationEight_pair_one37_unconditional
      hζ s hs
  have hpair :=
    equationEight_pair_one_generators_coprime37
      hζ s rhoPlus rhoMinus eta hplus hminus
  simpa only [pow_one] using
    exists_preparedEquationEightPair37 hζ s 1
      (by norm_num) rhoPlus rhoMinus rhoZero eta etaZero
      hetaReal
      (by simpa only [pow_one] using hplus)
      (by simpa only [pow_one] using hminus)
      hzero hconj hpair hminusNot

/-- Fully prepared historical pair at `2,-2`, with the unconditional
Takagi--Furtwängler input already discharged. -/
theorem exists_preparedEquationEightPair_two37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (s : HistoricalState hζ) (hs : RealSourceAdmissible hζ s)
    (rhoZero : 𝓞 K) (etaZero : (𝓞 K)ˣ)
    (hzero :
      s.omega + s.theta =
        etaZero * kappa hζ ^ (37 * s.m - 18) * rhoZero ^ 37) :
    Nonempty (PreparedEquationEightPair37 hζ s (hζ.unit' ^ 2)) := by
  obtain ⟨rhoPlus, rhoMinus, eta, hetaReal, hplus, hminus,
      hconj, -, hminusNot⟩ :=
    _root_.Fermat.ThirtySeven.TakagiHistorical37.exists_historicalEquationEight_pair_two37_unconditional
      hζ s hs
  have hpair :=
    equationEight_pair_two_generators_coprime37
      hζ s rhoPlus rhoMinus eta hplus hminus
  exact exists_preparedEquationEightPair37 hζ s 2
    (by norm_num) rhoPlus rhoMinus rhoZero eta etaZero
    hetaReal
    hplus hminus hzero hconj hpair hminusNot

end

end Fermat.ThirtySeven.VandiverHistorical
