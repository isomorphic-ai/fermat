/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Feeding the allocated Fermat equation (8) into the historical descent

The conservation development produces a literal equation-(8) generator
for the normalized factor of an oriented primitive Fermat state.  This
file identifies that factor with Vandiver's historical fixed-denominator
factor whenever the historical state has the same two linear entries.

The historical local calculation then proves that the coefficient unit is
real.  Conjugating the plus equation supplies the inverse-root equation
with the same unit, and the existing equation-(9) consumer prepares the
pair for the quadratic elimination.  Thus the only remaining input to this
adapter is the independently constructed equation-(8a) generator for the
same historical state.
-/
import Fermat.FiftyNine.Conservation.FermatStateEquationEight59
import Fermat.FiftyNine.VandiverHistoricalAssembly59

open scoped NumberField nonZeroDivisors Cyclotomic

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Fermat.FiftyNine.Conservation.FermatStateHistoricalDescent59

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverLemmaOne
open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.FermatStateEquationEight59
open Fermat.FiftyNine.Conservation.StateFactorConjugation
open Fermat.FiftyNine.Conservation.StateFactorPair
open Fermat.FiftyNine.VandiverHistorical

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 59) K (by norm_num)

variable {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}

/-- If a historical state has the two linear entries of the integral
Fermat state, its fixed-denominator factor at `zeta` is literally the
conservation layer's normalized plus factor. -/
theorem historicalZetaFactor_eq_normalizedPlusFactor59
    (s : HistoricalState hZeta)
    (homega : s.omega = (S.x : 𝓞 K))
    (htheta : s.theta = (S.y : 𝓞 K)) :
    historicalZetaFactor59 hZeta s =
      normalizedPlusFactor hZeta S hz := by
  have hpi : (hZeta.unit' : 𝓞 K) - 1 ≠ 0 :=
    hZeta.unit'_coe.sub_one_ne_zero (by norm_num)
  have hunitVal : (hZeta.unit' : 𝓞 K) = hZeta.toInteger := rfl
  apply mul_right_cancel₀ hpi
  calc
    historicalZetaFactor59 hZeta s *
          ((hZeta.unit' : 𝓞 K) - 1) =
        s.omega + s.theta * (hZeta.unit' : 𝓞 K) := by
      exact div_zeta_sub_one_mul_zeta_sub_one
        (by norm_num : 59 ≠ 2) hZeta
        (historicalState_regularEquation59 hZeta s)
        (zetaNthRoot (K := K) (p := 59) hZeta)
    _ = (S.x : 𝓞 K) + (S.y : 𝓞 K) *
          (hZeta.unit' : 𝓞 K) := by rw [homega, htheta]
    _ = normalizedPlusFactor hZeta S hz *
          ((hZeta.unit' : 𝓞 K) - 1) := by
      simpa only [Fermat.Conservation.KummerDrain.factorNode,
        fixedDenominator, hunitVal, mul_comm] using
          (normalizedPlusFactor_spec hZeta S hz).symm

/-- The literal statewise equation-(8) witness supplies Vandiver's paired
equations at `zeta,zeta⁻¹` with one common real unit.  The generators
are conjugate and both are prime to the ramified uniformizer. -/
theorem exists_historicalEquationEightPair_of_state59
    (pair : StateLinkedIdealPair hZeta S hz)
    (s : HistoricalState hZeta)
    (hs : RealSourceAdmissible hZeta s)
    (homega : s.omega = (S.x : 𝓞 K))
    (htheta : s.theta = (S.y : 𝓞 K)) :
    ∃ (rhoPlus rhoMinus : 𝓞 K) (eta : (𝓞 K)ˣ),
      NumberField.IsCMField.unitsComplexConj K eta = eta ∧
      s.omega + (hZeta.unit' : 𝓞 K) * s.theta =
        (1 - (hZeta.unit' : 𝓞 K)) * eta * rhoPlus ^ 59 ∧
      s.omega + (hZeta.unit'⁻¹ : (𝓞 K)ˣ) * s.theta =
        (1 - (hZeta.unit'⁻¹ : (𝓞 K)ˣ)) * eta * rhoMinus ^ 59 ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K rhoPlus = rhoMinus ∧
      ¬ (hZeta.unit' : 𝓞 K) - 1 ∣ rhoPlus ∧
      ¬ (hZeta.unit' : 𝓞 K) - 1 ∣ rhoMinus := by
  obtain ⟨rhoPlus, epsilon, -, hequation⟩ :=
    exists_normalizedPlusFactor_equationEight59 pair
  have hfactor : historicalZetaFactor59 hZeta s =
      normalizedPlusFactor hZeta S hz :=
    historicalZetaFactor_eq_normalizedPlusFactor59 s homega htheta
  have hhistorical : historicalZetaFactor59 hZeta s =
      epsilon * rhoPlus ^ 59 := by
    rw [hfactor]
    exact hequation
  have hepsilonReal :
      NumberField.IsCMField.unitsComplexConj K epsilon = epsilon :=
    historicalEquationEight_unit_real59
      hZeta s hs rhoPlus epsilon hhistorical
  have hepsilonRealVal :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (epsilon : 𝓞 K) = epsilon :=
    congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hepsilonReal
  let rhoMinus : 𝓞 K :=
    NumberField.IsCMField.ringOfIntegersComplexConj K rhoPlus
  let eta : (𝓞 K)ˣ := -epsilon
  have hetaReal : NumberField.IsCMField.unitsComplexConj K eta = eta := by
    apply Units.ext
    change NumberField.IsCMField.ringOfIntegersComplexConj K
      (-(epsilon : 𝓞 K)) = -(epsilon : 𝓞 K)
    rw [map_neg, hepsilonRealVal]
  have hunitVal : (hZeta.unit' : 𝓞 K) = hZeta.toInteger := rfl
  have hplus :
      s.omega + (hZeta.unit' : 𝓞 K) * s.theta =
        (1 - (hZeta.unit' : 𝓞 K)) * eta * rhoPlus ^ 59 := by
    calc
      s.omega + (hZeta.unit' : 𝓞 K) * s.theta =
          normalizedPlusFactor hZeta S hz *
            ((hZeta.unit' : 𝓞 K) - 1) := by
        rw [homega, htheta]
        simpa only [Fermat.Conservation.KummerDrain.factorNode,
          fixedDenominator, hunitVal, mul_comm] using
            (normalizedPlusFactor_spec hZeta S hz).symm
      _ = ((epsilon : 𝓞 K) * rhoPlus ^ 59) *
            ((hZeta.unit' : 𝓞 K) - 1) := by rw [hequation]
      _ = (1 - (hZeta.unit' : 𝓞 K)) * eta * rhoPlus ^ 59 := by
        dsimp [eta]
        ring
  have hzetaUnit : zetaUnit hZeta = hZeta.unit' := by
    apply Units.ext
    exact zetaUnit_val hZeta
  have hminusFactor : normalizedMinusFactor hZeta S hz =
      (-(hZeta.unit')⁻¹ * epsilon : (𝓞 K)ˣ) * rhoMinus ^ 59 := by
    rw [normalizedMinusFactor_eq_unit_mul_conj, hzetaUnit,
      hequation, map_mul, map_pow, hepsilonRealVal]
    dsimp [rhoMinus]
    ring
  have hminus :
      s.omega + (hZeta.unit'⁻¹ : (𝓞 K)ˣ) * s.theta =
        (1 - (hZeta.unit'⁻¹ : (𝓞 K)ˣ)) * eta * rhoMinus ^ 59 := by
    have hinv : (hZeta.unit' : 𝓞 K) *
        (hZeta.unit'⁻¹ : (𝓞 K)ˣ) = 1 := by
      rw [← Units.val_mul]
      simp
    have hcoefficient :
        ((-(hZeta.unit')⁻¹ * epsilon : (𝓞 K)ˣ) : 𝓞 K) *
            ((hZeta.unit' : 𝓞 K) - 1) =
          (1 - (hZeta.unit'⁻¹ : (𝓞 K)ˣ)) * (eta : 𝓞 K) := by
      dsimp [eta]
      linear_combination -(epsilon : 𝓞 K) * hinv
    calc
      s.omega + (hZeta.unit'⁻¹ : (𝓞 K)ˣ) * s.theta =
          normalizedMinusFactor hZeta S hz *
            ((hZeta.unit' : 𝓞 K) - 1) := by
        rw [homega, htheta]
        simpa only [Fermat.Conservation.KummerDrain.factorNode,
          fixedDenominator, hunitVal, hzetaUnit, mul_comm] using
            (normalizedMinusFactor_spec hZeta S hz).symm
      _ = (((-(hZeta.unit')⁻¹ * epsilon : (𝓞 K)ˣ) : 𝓞 K) *
            rhoMinus ^ 59) * ((hZeta.unit' : 𝓞 K) - 1) := by
        rw [hminusFactor]
      _ = (1 - (hZeta.unit'⁻¹ : (𝓞 K)ˣ)) * eta *
            rhoMinus ^ 59 := by
        rw [show
          (((-(hZeta.unit')⁻¹ * epsilon : (𝓞 K)ˣ) : 𝓞 K) *
                rhoMinus ^ 59) * ((hZeta.unit' : 𝓞 K) - 1) =
              (((-(hZeta.unit')⁻¹ * epsilon : (𝓞 K)ˣ) : 𝓞 K) *
                ((hZeta.unit' : 𝓞 K) - 1)) * rhoMinus ^ 59 by ring]
        rw [hcoefficient]
  have hrhoPlusNot : ¬ (hZeta.unit' : 𝓞 K) - 1 ∣ rhoPlus := by
    intro hrho
    apply historicalZetaFactor_not_ramified59 hZeta s hs
    rw [hhistorical]
    exact dvd_mul_of_dvd_right
      (dvd_pow (n := 59) hrho (by norm_num)) _
  have hrhoMinusNot : ¬ (hZeta.unit' : 𝓞 K) - 1 ∣ rhoMinus := by
    intro hrho
    have hc := zeta_sub_one_pow_dvd_conj_of_dvd59
      hZeta 1 rhoMinus (by simpa only [pow_one] using hrho)
    apply hrhoPlusNot
    have hinvol :
        NumberField.IsCMField.ringOfIntegersComplexConj K rhoMinus =
          rhoPlus := by
      dsimp [rhoMinus]
      apply NumberField.RingOfIntegers.ext
      exact NumberField.IsCMField.complexConj_apply_apply K rhoPlus
    simpa only [pow_one, hinvol] using hc
  exact ⟨rhoPlus, rhoMinus, eta, hetaReal, hplus, hminus,
    rfl, hrhoPlusNot, hrhoMinusNot⟩

/-- The strongest existing direct consumer of equation (8): once the
independent equation-(8a) generator for the same historical state is
given, the actual allocated Fermat witnesses pass through the difference
equation, equation (9a), real quotient-generator extraction, and unit
absorption, yielding a fully prepared pair for equation (10). -/
theorem exists_preparedEquationEightPair_one_of_state59
    (pair : StateLinkedIdealPair hZeta S hz)
    (s : HistoricalState hZeta)
    (hs : RealSourceAdmissible hZeta s)
    (homega : s.omega = (S.x : 𝓞 K))
    (htheta : s.theta = (S.y : 𝓞 K))
    (rhoZero : 𝓞 K) (etaZero : (𝓞 K)ˣ)
    (hzero :
      s.omega + s.theta =
        etaZero * kappa hZeta ^ (59 * s.m - 29) * rhoZero ^ 59) :
    Nonempty (PreparedEquationEightPair59 hZeta s hZeta.unit') := by
  obtain ⟨rhoPlus, rhoMinus, eta, hetaReal, hplus, hminus,
      hconj, -, hminusNot⟩ :=
    exists_historicalEquationEightPair_of_state59
      pair s hs homega htheta
  have hcoprime := equationEight_pair_one_generators_coprime59
    hZeta s rhoPlus rhoMinus eta hplus hminus
  simpa only [pow_one] using
    exists_preparedEquationEightPair59 hZeta s 1 (by norm_num)
      rhoPlus rhoMinus rhoZero eta etaZero hetaReal
      (by simpa only [pow_one] using hplus)
      (by simpa only [pow_one] using hminus)
      hzero hconj hcoprime hminusNot

/-- For a matching historical state, equation (8a) is already constructed
unconditionally.  Hence the allocated Fermat equation-(8) witness reaches
the fully prepared post-(9) pair without any additional arithmetic premise. -/
theorem exists_preparedEquationEightPair_one_of_state_unconditional59
    (pair : StateLinkedIdealPair hZeta S hz)
    (s : HistoricalState hZeta)
    (hs : RealSourceAdmissible hZeta s)
    (homega : s.omega = (S.x : 𝓞 K))
    (htheta : s.theta = (S.y : 𝓞 K)) :
    Nonempty (PreparedEquationEightPair59 hZeta s hZeta.unit') := by
  obtain ⟨rhoZero, etaZero, -, hzero, -, -, -⟩ :=
    exists_historicalEquationEightA59 hZeta s hs
  exact exists_preparedEquationEightPair_one_of_state59
    pair s hs homega htheta rhoZero etaZero hzero

/-- The oriented integral Fermat state itself supplies a matching initial
historical state with `m = 29`.  Combining that concrete start with the
literal equation-(8) bridge yields the prepared pair used by the first
historical reduction step. -/
theorem exists_initialHistoricalPreparedEquationEightPair_one59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ s : HistoricalState hZeta,
      RealSourceAdmissible hZeta s ∧
      s.omega = (S.x : 𝓞 K) ∧
      s.theta = (S.y : 𝓞 K) ∧
      s.m = 29 ∧
      Nonempty (PreparedEquationEightPair59 hZeta s hZeta.unit') := by
  obtain ⟨t, ht⟩ := hz
  have ht0 : t ≠ 0 := by
    intro ht0
    apply S.z_ne_zero
    rw [ht, ht0]
    simp
  obtain ⟨hxy, hyz, hxz⟩ :=
    Fermat.pairwiseCoprime_of_primitive_solution
      (by norm_num : 59 ≠ 0) S.x_ne_zero S.y_ne_zero S.z_ne_zero
      S.primitive S.equation
  obtain ⟨u, hu⟩ := kappa_pow_twentyNine_associated_59 hZeta
  have hkappa0 : kappa hZeta ^ 29 ≠ 0 :=
    (kappa_pow_twentyNine_associated_59 hZeta).ne_zero_iff.mpr
      (by norm_num)
  have huReal :
      NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K) = u := by
    have hconj := congrArg
      (NumberField.IsCMField.ringOfIntegersComplexConj K) hu
    simp only [map_mul, map_pow, ringOfIntegersComplexConj_kappa hZeta,
      map_ofNat] at hconj
    exact mul_left_cancel₀ hkappa0 (hconj.trans hu.symm)
  let xi : 𝓞 K := (u : 𝓞 K) * (t : 𝓞 K)
  have hyt : IsCoprime (S.y : 𝓞 K) (t : 𝓞 K) := by
    have hcast := hyz.intCast (R := 𝓞 K)
    rw [ht, Int.cast_mul] at hcast
    exact hcast.of_mul_right_right
  have hxt : IsCoprime (S.x : 𝓞 K) (t : 𝓞 K) := by
    have hcast := hxz.intCast (R := 𝓞 K)
    rw [ht, Int.cast_mul] at hcast
    exact hcast.of_mul_right_right
  let s : HistoricalState hZeta :=
    { omega := S.x
      theta := S.y
      xi := xi
      eta := 1
      m := 29
      one_lt_m := by norm_num
      xi_ne_zero := by
        dsimp [xi]
        exact mul_ne_zero u.isUnit.ne_zero (Int.cast_ne_zero.mpr ht0)
      coprime_omega_theta := hxy.intCast
      coprime_theta_xi := by
        dsimp [xi]
        exact (isCoprime_mul_unit_left_right u.isUnit
          (S.y : 𝓞 K) (t : 𝓞 K)).mpr hyt
      coprime_omega_xi := by
        dsimp [xi]
        exact (isCoprime_mul_unit_left_right u.isUnit
          (S.x : 𝓞 K) (t : 𝓞 K)).mpr hxt
      equation := by
        simp only [Units.val_one, one_mul]
        calc
          (S.x : 𝓞 K) ^ 59 + (S.y : 𝓞 K) ^ 59 =
              (S.z : 𝓞 K) ^ 59 := stateEquation S
          _ = ((((59 : ℤ) * t : ℤ) : 𝓞 K)) ^ 59 := by rw [ht]
          _ = ((59 : 𝓞 K) * (t : 𝓞 K)) ^ 59 := by norm_num
          _ = (kappa hZeta ^ 29 *
              ((u : 𝓞 K) * (t : 𝓞 K))) ^ 59 := by
            congr 1
            rw [← mul_assoc, hu]
          _ = (kappa hZeta ^ 29 * xi) ^ 59 := rfl }
  have hs : RealSourceAdmissible hZeta s := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp [s]
      simp
    · dsimp [s]
      simp
    · dsimp [s, xi]
      simp [huReal]
    · dsimp [s]
      simp
  have hprepared :
      Nonempty (PreparedEquationEightPair59 hZeta s hZeta.unit') :=
    exists_preparedEquationEightPair_one_of_state_unconditional59
      pair s hs rfl rfl
  exact ⟨s, hs, rfl, rfl, rfl, hprepared⟩

/-- Apply the same statewise equation-(8) bridge at the primitive root
`zeta^2`, then transport the prepared data back to the original historical
state.  This supplies the second conjugate pair required by equation (10),
again from the allocated Fermat factors rather than a separate Lemma-I
input. -/
theorem exists_preparedEquationEightPair_two_of_state_unconditional59
    (hz : (59 : ℤ) ∣ S.z)
    (s : HistoricalState hZeta)
    (hs : RealSourceAdmissible hZeta s)
    (homega : s.omega = (S.x : 𝓞 K))
    (htheta : s.theta = (S.y : 𝓞 K)) :
    Nonempty
      (PreparedEquationEightPair59 hZeta s (hZeta.unit' ^ 2)) := by
  let hTwo : IsPrimitiveRoot (zeta ^ 2) 59 :=
    hZeta.pow_of_coprime 2 (by norm_num)
  let sTwo : HistoricalState hTwo := historicalStateAtTwo59 hZeta s
  have hsTwo : RealSourceAdmissible hTwo sTwo := by
    simpa only [hTwo, sTwo] using
      historicalStateAtTwo_admissible59 hZeta s hs
  let pairTwo : StateLinkedIdealPair hTwo S hz :=
    allocatedPair hTwo S hz
  obtain ⟨d⟩ :=
    exists_preparedEquationEightPair_one_of_state_unconditional59
      pairTwo sTwo hsTwo
        (by simpa only [sTwo, historicalStateAtTwo59] using homega)
        (by simpa only [sTwo, historicalStateAtTwo59] using htheta)
  have hassoc :
      Associated ((hZeta.unit' : 𝓞 K) - 1)
        ((hTwo.unit' : 𝓞 K) - 1) := by
    simpa only [hTwo, powTwoPrimitiveRoot_unit59 hZeta,
      Units.val_pow_eq_pow_val] using
      hZeta.unit'_coe.associated_sub_one_pow_sub_one_of_coprime
        (by norm_num : Nat.Coprime 2 59)
  let D : ℕ := (2 * s.m - 2) * 59
  have hassocPow :
      Associated (((hZeta.unit' : 𝓞 K) - 1) ^ D)
        (((hTwo.unit' : 𝓞 K) - 1) ^ D) := by
    obtain ⟨v, hv⟩ := hassoc
    refine ⟨v ^ D, ?_⟩
    simp only [Units.val_pow_eq_pow_val]
    rw [← mul_pow, hv]
  refine ⟨
    { rplus := d.rplus
      rminus := d.rminus
      mu := d.mu
      coefficient := d.coefficient
      coefficient_real := d.coefficient_real
      equation_plus := by
        simpa only [sTwo, historicalStateAtTwo59, hTwo,
          powTwoPrimitiveRoot_unit59 hZeta,
          Units.val_pow_eq_pow_val] using d.equation_plus
      equation_minus := by
        simpa only [sTwo, historicalStateAtTwo59, hTwo,
          powTwoPrimitiveRoot_unit59 hZeta] using d.equation_minus
      conjugate := d.conjugate
      rplus_not_ramified := fun h ↦
        d.rplus_not_ramified ((hassoc.dvd_iff_dvd_left).mp h)
      rminus_not_ramified := fun h ↦
        d.rminus_not_ramified ((hassoc.dvd_iff_dvd_left).mp h)
      mu_real := d.mu_real
      mu_not_ramified := fun h ↦
        d.mu_not_ramified ((hassoc.dvd_iff_dvd_left).mp h)
      close_plus := by
        apply hassocPow.dvd_iff_dvd_left.mpr
        simpa only [D, sTwo, historicalStateAtTwo59] using d.close_plus
      close_minus := by
        apply hassocPow.dvd_iff_dvd_left.mpr
        simpa only [D, sTwo, historicalStateAtTwo59] using d.close_minus }⟩

/-- Assemble two supplied prepared pairs into the exact historical
reduction datum.  This is the equation-(10) consumer factored out with the
pairs as genuine inputs, so the statewise equation-(8) bridge remains on
the proof path instead of being bypassed by the older monolithic theorem. -/
theorem exists_conjugationPowerReductionData_of_preparedPairs59
    (s : HistoricalState hZeta)
    (hs : RealSourceAdmissible hZeta s)
    (dOne : PreparedEquationEightPair59 hZeta s hZeta.unit')
    (dTwo : PreparedEquationEightPair59 hZeta s (hZeta.unit' ^ 2)) :
    Nonempty (ConjugationPowerReductionData59 hZeta s) := by
  obtain ⟨rhoZero, etaZero, jZero, hzero, hgenerator,
      hconjZero, hetaZeroReal⟩ :=
    exists_historicalEquationEightA59 hZeta s hs
  let D : ℕ := (2 * s.m - 2) * 59
  have hcoefficient :
      ((hZeta.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) * dOne.rplus ^ 59 -
          (dTwo.coefficient : 𝓞 K) * dTwo.rplus ^ 59 := by
    simpa only [D] using
      historicalEquationEight_one_two_coefficients_close59
        hZeta s hs dOne.rplus dTwo.rplus
        dOne.coefficient dTwo.coefficient
        dOne.equation_plus dTwo.equation_plus
  have hpowOne :
      ((hZeta.unit' : 𝓞 K) - 1) ^ D ∣
        dOne.rplus ^ 59 - dOne.mu ^ 3481 := by
    have h := dOne.close_plus.trans
      (sub_dvd_pow_sub_pow dOne.rplus (dOne.mu ^ 59) 59)
    simpa only [D, ← pow_mul] using h
  have hpowTwo :
      ((hZeta.unit' : 𝓞 K) - 1) ^ D ∣
        dTwo.rplus ^ 59 - dTwo.mu ^ 3481 := by
    have h := dTwo.close_plus.trans
      (sub_dvd_pow_sub_pow dTwo.rplus (dTwo.mu ^ 59) 59)
    simpa only [D, ← pow_mul] using h
  have herrors :
      ((hZeta.unit' : 𝓞 K) - 1) ^ D ∣
        (dOne.coefficient : 𝓞 K) *
            (dOne.rplus ^ 59 - dOne.mu ^ 3481) -
          (dTwo.coefficient : 𝓞 K) *
            (dTwo.rplus ^ 59 - dTwo.mu ^ 3481) :=
    dvd_sub
      (dvd_mul_of_dvd_right hpowOne (dOne.coefficient : 𝓞 K))
      (dvd_mul_of_dvd_right hpowTwo (dTwo.coefficient : 𝓞 K))
  have hmuD :
      ((hZeta.unit' : 𝓞 K) - 1) ^ D ∣
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
      ((hZeta.unit' : 𝓞 K) - 1) ^ 118 ∣
        (dOne.coefficient : 𝓞 K) * dOne.mu ^ 3481 -
          (dTwo.coefficient : 𝓞 K) * dTwo.mu ^ 3481 :=
    (pow_dvd_pow ((hZeta.unit' : 𝓞 K) - 1) h118D).trans hmuD
  obtain ⟨c, hratio3481⟩ :=
    exists_int_ratio_pow3481_congruent59 hZeta
      dOne.coefficient dTwo.coefficient dOne.mu dTwo.mu
      dOne.mu_real dTwo.mu_real dOne.mu_not_ramified hmu118
  obtain ⟨rationalBase, hnegativeRatio⟩ :=
    exists_int_negative_square_ratio_pow59_congruent59 hZeta
      (dOne.coefficient / dTwo.coefficient) c hratio3481
  let minusOne : (𝓞 K)ˣ := -1
  let epsilonOne : (𝓞 K)ˣ :=
    minusOne *
      (equationTenTraceTwoUnit59 hZeta * dOne.coefficient ^ 2)
  let epsilonTwo : (𝓞 K)ˣ :=
    equationTenTraceTwoUnit59 hZeta * dTwo.coefficient ^ 2
  let epsilonThree : (𝓞 K)ˣ :=
    minusOne * (equationTenTraceOneUnit59 hZeta * etaZero ^ 2)
  have hepsilonRatio :
      epsilonOne / epsilonTwo =
        -((dOne.coefficient / dTwo.coefficient) ^ 2) := by
    have hgroup :
        minusOne *
              (equationTenTraceTwoUnit59 hZeta *
                dOne.coefficient ^ 2) /
            (equationTenTraceTwoUnit59 hZeta *
              dTwo.coefficient ^ 2) =
          minusOne *
            (dOne.coefficient / dTwo.coefficient) ^ 2 := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        minusOne *
              (equationTenTraceTwoUnit59 hZeta *
                dOne.coefficient ^ 2) *
              (dTwo.coefficient⁻¹ ^ 2 *
                (equationTenTraceTwoUnit59 hZeta)⁻¹) =
            minusOne *
              (equationTenTraceTwoUnit59 hZeta *
                (equationTenTraceTwoUnit59 hZeta)⁻¹) *
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
                (equationTenTraceTwoUnit59 hZeta *
                  dOne.coefficient ^ 2) /
              (equationTenTraceTwoUnit59 hZeta *
                dTwo.coefficient ^ 2) := by
            rfl
      _ = minusOne *
          (dOne.coefficient / dTwo.coefficient) ^ 2 := hgroup
      _ = -((dOne.coefficient / dTwo.coefficient) ^ 2) := by
        dsimp [minusOne]
        ext
        simp
  have hhigh :
      ((1 : 𝓞 K) - hZeta.unit') ^ 118 ∣
        (((epsilonOne / epsilonTwo : (𝓞 K)ˣ) : 𝓞 K) -
          (rationalBase : 𝓞 K) ^ 59) := by
    rw [hepsilonRatio]
    exact hnegativeRatio
  have hquadOne := dOne.quadraticEquation_one hZeta s
  have hquadTwo := dTwo.quadraticEquation_two hZeta s
  have hquadZero :=
    historicalEquationEightA_quadratic59
      hZeta s rhoZero etaZero hzero
  have hweightedRaw :=
    equationTenB_commonKappa59 hZeta s.omega s.theta
      (dOne.rplus * dOne.rminus)
      (dTwo.rplus * dTwo.rminus)
      (kappa hZeta ^ (2 * s.m - 1) * rhoZero ^ 2)
      (dOne.coefficient ^ 2)
      (equationTenTraceTwoUnit59 hZeta * dTwo.coefficient ^ 2)
      (etaZero ^ 2)
      hquadOne hquadTwo hquadZero
  have hweighted :
      epsilonOne * (dOne.rplus * dOne.rminus) ^ 59 +
          epsilonTwo * (dTwo.rplus * dTwo.rminus) ^ 59 =
        epsilonThree *
          (kappa hZeta ^ (2 * s.m - 1) * rhoZero ^ 2) ^ 59 := by
    dsimp [epsilonOne, epsilonTwo, epsilonThree, minusOne]
    have hweightedRaw' := hweightedRaw
    simp only [Units.val_mul, Units.val_neg,
      Units.val_pow_eq_pow_val] at hweightedRaw'
    linear_combination -hweightedRaw'
  have hrhoZero : rhoZero ≠ 0 := by
    intro hrho
    apply historicalState_omega_add_theta_ne_zero59 hZeta s
    rw [hzero, hrho]
    norm_num
  have hcop :=
    equationEight_generators_products_coprime59 hZeta
      dOne.coefficient dOne.coefficient
      dTwo.coefficient dTwo.coefficient
      ((etaZero : 𝓞 K) * kappa hZeta ^ (59 * s.m - 29))
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
      equationTenTraceOneUnit_real59 hZeta, hetaZeroReal]
  have hepsilonTwoReal :
      NumberField.IsCMField.unitsComplexConj K epsilonTwo =
        epsilonTwo := by
    dsimp [epsilonTwo]
    rw [map_mul, map_pow,
      equationTenTraceTwoUnit_real59 hZeta, dTwo.coefficient_real]
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
        simpa using dOne.product_real hZeta s hZeta.unit'
      conjugation_y := by
        simpa using dTwo.product_real hZeta s (hZeta.unit' ^ 2)
      conjugation_z := hconjZero
      real_eta := hrealEta
      factorSupport_strict :=
        historicalEquationEightA_square_support_strict_unconditional59
          hZeta s hs rhoZero hgenerator }⟩

/-- Both prepared equation-(8) pairs needed by the first quadratic
elimination are therefore available on the concrete initial state. -/
theorem exists_initialHistoricalPreparedEquationEightPairs59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ s : HistoricalState hZeta,
      RealSourceAdmissible hZeta s ∧
      s.omega = (S.x : 𝓞 K) ∧
      s.theta = (S.y : 𝓞 K) ∧
      s.m = 29 ∧
      Nonempty (PreparedEquationEightPair59 hZeta s hZeta.unit') ∧
      Nonempty
        (PreparedEquationEightPair59 hZeta s (hZeta.unit' ^ 2)) := by
  obtain ⟨s, hs, homega, htheta, hm, hOne⟩ :=
    exists_initialHistoricalPreparedEquationEightPair_one59 pair
  have hTwo :=
    exists_preparedEquationEightPair_two_of_state_unconditional59
      hz s hs homega htheta
  exact ⟨s, hs, homega, htheta, hm, hOne, hTwo⟩

/-- The two conservation-derived prepared pairs assemble into the complete
equations-(7)--(10) datum for the actual initial historical state. -/
theorem exists_initialHistoricalReductionData59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (s : HistoricalState hZeta)
        (_d : EquationSevenToTenData hZeta (RealSourceAdmissible hZeta) s),
      RealSourceAdmissible hZeta s ∧
      s.omega = (S.x : 𝓞 K) ∧
      s.theta = (S.y : 𝓞 K) ∧
      s.m = 29 := by
  obtain ⟨s, hs, homega, htheta, hm, ⟨dOne⟩, ⟨dTwo⟩⟩ :=
    exists_initialHistoricalPreparedEquationEightPairs59 pair
  obtain ⟨raw⟩ :=
    exists_conjugationPowerReductionData_of_preparedPairs59
      s hs dOne dTwo
  let weighted : WeightedReductionData59 hZeta s :=
    weightedReductionData_of_conjugationPowers59 hZeta raw
  let d : EquationSevenToTenData hZeta (RealSourceAdmissible hZeta) s :=
    equationSevenToTenData_of_weighted59 hZeta weighted
  exact ⟨s, d, hs, homega, htheta, hm⟩

/-- **Actual first historical successor.**  Vandiver's proved deep-unit
lemma turns the reduction datum produced from the literal equation-(8)
witnesses into an admissible state of exponent `57` with strictly smaller
prime-ideal support.  This is the historical support descent; it does not
claim a decrease of the separate integral hypotenuse charge. -/
theorem exists_initialHistoricalStrictSuccessor59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ (s next : HistoricalState hZeta),
      RealSourceAdmissible hZeta s ∧
      s.omega = (S.x : 𝓞 K) ∧
      s.theta = (S.y : 𝓞 K) ∧
      s.m = 29 ∧
      RealSourceAdmissible hZeta next ∧
      next.m = 57 ∧
      distinctPrimeIdealFactorCount next.xi <
        distinctPrimeIdealFactorCount s.xi := by
  obtain ⟨s, d, hs, homega, htheta, hm⟩ :=
    exists_initialHistoricalReductionData59 pair
  have hkummer :
      KummerUnitPowerConclusion K 59 :=
    Fermat.Irregular.VandiverUnitLemma.kummerUnitPowerConclusion_of_lemmaTwo
      (by norm_num)
      (Fermat.FiftyNine.VandiverLemmaTwo.vandiverLemmaTwo_fiftyNine
        (K := K))
      Fermat.FiftyNine.ArithmeticCertificate.bernoulliCubeCondition_fiftyNine
  obtain ⟨v, hv⟩ := hkummer hZeta d.quotientUnit
    ⟨d.rationalBase, d.highCongruence⟩
  let next : HistoricalState hZeta := d.nextState v hv
  have hnextAdmissible : RealSourceAdmissible hZeta next :=
    d.next_admissible v hv
  have hnextM : next.m = 57 := by
    have h := d.next_exponent v hv
    dsimp only [next]
    rw [h, hm]
  have hdecrease :
      distinctPrimeIdealFactorCount next.xi <
        distinctPrimeIdealFactorCount s.xi := by
    exact d.factorCount_decreases v hv
  exact ⟨s, next, hs, homega, htheta, hm,
    hnextAdmissible, hnextM, hdecrease⟩

/-- The conservation-derived first successor can be fed into the already
proved uniform continuation of Vandiver's historical descent.  Its
well-founded support decrease rules out the original allocated Fermat
state. -/
theorem false_of_stateLinkedIdealPair_historicalDescent59
    (pair : StateLinkedIdealPair hZeta S hz) : False := by
  obtain ⟨-, next, -, -, -, -, hnext, -, -⟩ :=
    exists_initialHistoricalStrictSuccessor59 pair
  have hkummer : KummerUnitPowerConclusion K 59 :=
    Fermat.Irregular.VandiverUnitLemma.kummerUnitPowerConclusion_of_lemmaTwo
      (by norm_num)
      (Fermat.FiftyNine.VandiverLemmaTwo.vandiverLemmaTwo_fiftyNine
        (K := K))
      Fermat.FiftyNine.ArithmeticCertificate.bernoulliCubeCondition_fiftyNine
  have hreduce :
      EquationsSevenToTenReduction hZeta (RealSourceAdmissible hZeta) :=
    equationsSevenToTenReduction_59 hZeta
      (realPrincipalGeneratorElimination59 hZeta)
  exact no_historicalState hZeta (RealSourceAdmissible hZeta)
    hreduce hkummer ⟨next, hnext⟩

/-- No oriented primitive second-case state survives the literal
equation-(8) route. -/
theorem not_exists_orientedPrimitiveSecondCaseSolution59 :
    IsPrimitiveRoot zeta 59 →
    ¬ ∃ (S : PrimitiveSecondCaseSolution), (59 : ℤ) ∣ S.z := by
  intro hZeta
  rintro ⟨S, hz⟩
  exact false_of_stateLinkedIdealPair_historicalDescent59
    (allocatedPair hZeta S hz)

/-- Every primitive second-case state has an oriented rotation, so the
preceding contradiction empties the entire conservation state type. -/
theorem no_primitiveSecondCaseSolution59 :
    IsPrimitiveRoot zeta 59 →
    ¬ Nonempty PrimitiveSecondCaseSolution := by
  intro hZeta
  rintro ⟨S⟩
  obtain ⟨T, hT⟩ := S.exists_oriented
  exact not_exists_orientedPrimitiveSecondCaseSolution59 hZeta ⟨T, hT⟩

/-- Second case at exponent `59`, now with the newly connected statewise
equation-(8) witnesses explicitly on the proof path. -/
theorem secondCaseExcluded_fiftyNine_via_stateEquationEight :
    IsPrimitiveRoot zeta 59 →
    Fermat.SecondCaseExcluded 59 := by
  intro hZeta a b c ha hb hc hgcd hcase hequation
  apply no_primitiveSecondCaseSolution59 hZeta
  exact ⟨
    { x := a
      y := b
      z := c
      x_ne_zero := ha
      y_ne_zero := hb
      z_ne_zero := hc
      primitive := hgcd
      equation := hequation
      secondCase := hcase }⟩

/-- End-to-end FLT at exponent `59` with the conservation equation-(8)
bridge used for Case II and the existing Sophie-Germain computation used
for Case I. -/
theorem holdsAt_fiftyNine_via_stateEquationEight : Fermat.HoldsAt 59 := by
  letI : NeZero (59 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {59} ℚ (CyclotomicField 59 ℚ) :=
    CyclotomicField.isCyclotomicExtension 59 ℚ
  obtain ⟨zeta, hZeta⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 59 ℚ)
      (Set.mem_singleton 59) (by norm_num : 59 ≠ 0)
  exact Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    (by norm_num) (by norm_num) (by norm_num)
    Fermat.FiftyNine.noConsecutivePowers_59_827
    Fermat.FiftyNine.exponentNotPower_59_827
    (secondCaseExcluded_fiftyNine_via_stateEquationEight hZeta)

end Fermat.FiftyNine.Conservation.FermatStateHistoricalDescent59
