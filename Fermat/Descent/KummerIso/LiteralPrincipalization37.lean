import Fermat.Descent.KummerIso.Principalization
import Fermat.Descent.Irregular.VandiverPreparedPairPrime

/-!
# Literal repair of the first regular Case-II break

This file deliberately works with the ideals chosen by
`FltRegular.CaseII.InductionStep`, rather than replacing the regular
induction by the historical descent.

For a real historical state the old distinguished root `η₀` is `1`.
Consequently, the two roots selected by the literal old proof are `ζ` and
`ζ²`.  The plus-class/Takagi construction principalizes the allocated root
at `ζ` directly.  At `ζ²`, its equation-(8) generator is first compared
with the *old fixed-denominator factor* `(ω + ζ² θ) / (ζ - 1)`.  Equality
of their `p`-th ideal powers then identifies the old allocated root with a
principal ideal.  This last identification uses injectivity of powers in
the monoid of integral ideals, not regularity of the full class group.

Thus the two conclusions below have exactly the types consumed by the old
`isPrincipal_a_div_a_zero` construction.
-/

namespace Fermat.KummerIso.LiteralPrincipalization37

open scoped NumberField nonZeroDivisors

open Polynomial
open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime
open Fermat.Irregular.VandiverHistoricalStatePrime
open Fermat.Irregular.VandiverHistoricalEquationEightAPrime
open Fermat.Irregular.VandiverEquationEightAFactorizationPrime
open Fermat.Irregular.VandiverGeneratorSupportPrime
open Fermat.Irregular.VandiverLemmaOne
open Fermat.Irregular.VandiverTakagiPairPrime
open Fermat.Irregular.VandiverPreparedPairPrime
open Fermat.KummerIso.Principalization

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [NumberField.IsCMField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- The literal first adjacent root used in the old Case-II induction:
`η₁ = η₀ ζ`. -/
noncomputable def oldEtaOne
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (s : HistoricalState hζ) :
    nthRootsFinset 37 (1 : 𝓞 K) := by
  let e := historicalState_regularEquation hζ s
  let hy := historicalState_theta_not_dvd hζ s
  let η₀ := zeta_sub_one_dvd_root (by norm_num : 37 ≠ 2) hζ e hy
  have hmem :=
    mul_mem_nthRootsFinset η₀.prop
      (hζ.unit'_coe.mem_nthRootsFinset (by norm_num))
  rw [one_mul] at hmem
  exact ⟨η₀ * hζ.unit', hmem⟩

/-- The literal second adjacent root used in the old Case-II induction:
`η₂ = η₀ ζ ζ`. -/
noncomputable def oldEtaTwo
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (s : HistoricalState hζ) :
    nthRootsFinset 37 (1 : 𝓞 K) := by
  have hmem :=
    mul_mem_nthRootsFinset (oldEtaOne hζ s).prop
      (hζ.unit'_coe.mem_nthRootsFinset (by norm_num))
  rw [one_mul] at hmem
  exact ⟨(oldEtaOne hζ s : 𝓞 K) * hζ.unit', hmem⟩

/-- In a real state, the first old adjacent root is literally `ζ`. -/
theorem oldEtaOne_eq_zetaNthRoot
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    oldEtaOne hζ s = zetaNthRoot hζ := by
  apply Subtype.ext
  change
    (zeta_sub_one_dvd_root
          (by norm_num : 37 ≠ 2) hζ
          (historicalState_regularEquation hζ s)
          (historicalState_theta_not_dvd hζ s) : 𝓞 K) *
        hζ.unit' =
      hζ.unit'
  rw [distinguishedRoot_eq_one_of_real
    (by norm_num : 37 ≠ 2) hζ
    (historicalState_regularEquation hζ s)
    (historicalState_theta_not_dvd hζ s) hs.1 hs.2.1]
  simp [oneNthRoot]

/-- In a real state, the second old adjacent root is literally `ζ²`. -/
theorem oldEtaTwo_val
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    (oldEtaTwo hζ s : 𝓞 K) = (hζ.unit' ^ 2 : (𝓞 K)ˣ) := by
  change (oldEtaOne hζ s : 𝓞 K) * hζ.unit' =
    (hζ.unit' ^ 2 : (𝓞 K)ˣ)
  rw [oldEtaOne_eq_zetaNthRoot hζ s hs]
  simp only [zetaNthRoot, pow_two, Units.val_mul]

/-- Takagi--Furtwängler principalizes the first allocated root selected by
the literal old induction. -/
theorem oldEtaOneRoot_isPrincipal
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (hplus : PlusClassNondivisibility K 37)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Submodule.IsPrincipal
      (root_div_zeta_sub_one_dvd_gcd
          (by norm_num : 37 ≠ 2) hζ
          (historicalState_regularEquation hζ s)
          (historicalState_theta_not_dvd hζ s)
          (oldEtaOne hζ s) :
        Ideal (𝓞 K)) := by
  rw [oldEtaOne_eq_zetaNthRoot hζ s hs]
  simpa only [historicalZetaFactorIdeal] using
    historicalZetaFactorIdeal_isPrincipal_of_plusClass
      (K := K) (p := 37) (by norm_num) hζ hplus s hs

set_option maxRecDepth 50000 in
/-- Takagi's equation-(8) generator at `ζ²` principalizes the *literal old*
allocated root at `η₂ = η₀ ζ ζ`.

The transported historical construction uses denominator `ζ² - 1`, while
the old regular proof keeps denominator `ζ - 1`.  These differ by a unit.
The proof below performs that comparison at the equation level and then
cancels `p`-th powers in the free ideal monoid. -/
theorem oldEtaTwoRoot_isPrincipal
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (hplus : PlusClassNondivisibility K 37)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Submodule.IsPrincipal
      (root_div_zeta_sub_one_dvd_gcd
          (by norm_num : 37 ≠ 2) hζ
          (historicalState_regularEquation hζ s)
          (historicalState_theta_not_dvd hζ s)
          (oldEtaTwo hζ s) :
        Ideal (𝓞 K)) := by
  let e := historicalState_regularEquation hζ s
  let hy := historicalState_theta_not_dvd hζ s
  let η₂ := oldEtaTwo hζ s
  let q₂ : 𝓞 K :=
    div_zeta_sub_one (by norm_num : 37 ≠ 2) hζ e η₂
  let I₂ : Ideal (𝓞 K) :=
    root_div_zeta_sub_one_dvd_gcd
      (by norm_num : 37 ≠ 2) hζ e hy η₂
  obtain ⟨pair⟩ :=
    exists_historicalEquationEightPair_two_of_plusClass
      (K := K) (p := 37) (by norm_num) hplus hζ s hs
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  have hπ0 : π ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero (by norm_num)
  have hqmul :
      q₂ * π =
        s.omega + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * s.theta := by
    have h :=
      div_zeta_sub_one_mul_zeta_sub_one
        (by norm_num : 37 ≠ 2) hζ e η₂
    simpa only [q₂, π, e, η₂, oldEtaTwo_val hζ s hs,
      Units.val_pow_eq_pow_val, mul_comm s.theta] using h
  have hcoefficient :
      Associated
        ((1 - (hζ.unit' : 𝓞 K) ^ 2) *
          (pair.coefficient : 𝓞 K))
        π := by
    simpa only [π] using
      associated_one_sub_zetaPow_mul_unit hζ 2
        (by norm_num) (by norm_num) pair.coefficient
  have hqAssociated :
      Associated q₂ (pair.rplus ^ 37) := by
    apply Associated.of_mul_right _ (Associated.refl π) hπ0
    have hleft :
        q₂ * π =
          ((1 - (hζ.unit' : 𝓞 K) ^ 2) *
            (pair.coefficient : 𝓞 K)) *
              pair.rplus ^ 37 := by
      rw [hqmul, pair.equation_plus]
      simp only [Units.val_pow_eq_pow_val]
    rw [hleft]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      hcoefficient.mul_mul (Associated.refl (pair.rplus ^ 37))
  have hIpow :
      I₂ ^ 37 = (Ideal.span {pair.rplus}) ^ 37 := by
    calc
      I₂ ^ 37 = Ideal.span {q₂} := by
        simpa only [I₂, q₂, e, hy, η₂] using
          (linearFactorQuotient_span_eq_factorRoot_pow
            (by norm_num : 37 ≠ 2) hζ e hy
            s.coprime_omega_theta η₂).symm
      _ = Ideal.span {pair.rplus ^ 37} :=
        Ideal.span_singleton_eq_span_singleton.mpr hqAssociated
      _ = (Ideal.span {pair.rplus}) ^ 37 :=
        (Ideal.span_singleton_pow pair.rplus 37).symm
  have hI :
      I₂ = Ideal.span {pair.rplus} :=
    pow_left_injective (M := Ideal (𝓞 K))
      (by norm_num : 37 ≠ 0) hIpow
  change Submodule.IsPrincipal (I₂ : Ideal (𝓞 K))
  rw [hI]
  exact ⟨⟨pair.rplus, rfl⟩⟩

/-- The residual ideal `𝔞₀` appearing literally in the old Case-II proof is
principal from the same plus-class certificate. -/
theorem oldResidualRoot_isPrincipal
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (hplus : PlusClassNondivisibility K 37)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Submodule.IsPrincipal
      (a_eta_zero_dvd_p_pow
          (by norm_num : 37 ≠ 2) hζ
          (historicalState_regularEquation hζ s)
          (historicalState_theta_not_dvd hζ s) :
        Ideal (𝓞 K)) := by
  simpa only [historicalEquationEightAIdeal] using
    historicalResidualIdeal_isPrincipal_of_plusClass
      (K := K) (p := 37) (by norm_num) hζ hplus s hs

/-- Repair #1 in exactly the pair of types needed by the old construction:
both `𝔞(η₁)/𝔞₀` and `𝔞(η₂)/𝔞₀` are principal fractional ideals. -/
theorem oldAdjacentRootQuotients_arePrincipal
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
    (hplus : PlusClassNondivisibility K 37)
    (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    Submodule.IsPrincipal
        (((root_div_zeta_sub_one_dvd_gcd
              (by norm_num : 37 ≠ 2) hζ
              (historicalState_regularEquation hζ s)
              (historicalState_theta_not_dvd hζ s)
              (oldEtaOne hζ s) /
            a_eta_zero_dvd_p_pow
              (by norm_num : 37 ≠ 2) hζ
              (historicalState_regularEquation hζ s)
              (historicalState_theta_not_dvd hζ s) :
                FractionalIdeal (𝓞 K)⁰ K) :
          Submodule (𝓞 K) K)) ∧
      Submodule.IsPrincipal
        (((root_div_zeta_sub_one_dvd_gcd
              (by norm_num : 37 ≠ 2) hζ
              (historicalState_regularEquation hζ s)
              (historicalState_theta_not_dvd hζ s)
              (oldEtaTwo hζ s) /
            a_eta_zero_dvd_p_pow
              (by norm_num : 37 ≠ 2) hζ
              (historicalState_regularEquation hζ s)
              (historicalState_theta_not_dvd hζ s) :
                FractionalIdeal (𝓞 K)⁰ K) :
          Submodule (𝓞 K) K)) := by
  have hzero := oldResidualRoot_isPrincipal hζ hplus s hs
  exact
    ⟨selectedIdealQuotient_isPrincipal_of_ideals
        (oldEtaOneRoot_isPrincipal hζ hplus s hs) hzero,
      selectedIdealQuotient_isPrincipal_of_ideals
        (oldEtaTwoRoot_isPrincipal hζ hplus s hs) hzero⟩

end

end Fermat.KummerIso.LiteralPrincipalization37
