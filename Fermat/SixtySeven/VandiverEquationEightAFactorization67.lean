import Fermat.SixtySeven.VandiverGeneratorSupport67

/-!
# Vandiver's equation-(8a) factorization at exponent 67

This file formalizes the strict ideal-support step on pp. 623–624 of
Vandiver's 1929 proof.  The complement consists of all allocated linear
factors other than the distinguished real factor.  Its nontriviality is the
historical exceptional-case argument using conjugation and ramification.
-/

namespace Fermat.SixtySeven.VandiverHistorical

open scoped NumberField nonZeroDivisors BigOperators
open Polynomial
open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverCriterion
open Fermat.Irregular.VandiverLemmaOne

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {67} ℚ K]

local instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 67) K (by norm_num)

noncomputable def historicalEquationEightAComplement67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (s : HistoricalState hζ) : Ideal (𝓞 K) :=
  by
    classical
    let e := historicalState_regularEquation67 hζ s
    let hy := historicalState_theta_not_dvd67 hζ s
    let root := fun η : nthRootsFinset 67 (1 : 𝓞 K) ↦
      root_div_zeta_sub_one_dvd_gcd
        (K := K) (p := 67) (x := s.omega) (y := s.theta)
        (z := s.xi) (ε := historicalRegularUnit67 hζ s)
        (m := 2 * s.m - 1) (by norm_num) hζ e hy η
    let η₀ := zeta_sub_one_dvd_root
      (K := K) (p := 67) (x := s.omega) (y := s.theta)
      (z := s.xi) (ε := historicalRegularUnit67 hζ s)
      (m := 2 * s.m - 1) (by norm_num) hζ e hy
    exact
      ∏ η ∈ Finset.attach (nthRootsFinset 67 (1 : 𝓞 K)) \ {η₀}, root η

set_option maxRecDepth 4000 in
theorem historicalEquationEightA_factorization_and_coprime67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (s : HistoricalState hζ) (hs : RealSourceAdmissible hζ s) :
    Ideal.span {s.xi} =
        historicalEquationEightAIdeal67 hζ s *
          historicalEquationEightAComplement67 hζ s ∧
      IsCoprime (historicalEquationEightAIdeal67 hζ s)
        (historicalEquationEightAComplement67 hζ s) := by
  classical
  let e := historicalState_regularEquation67 hζ s
  let hy := historicalState_theta_not_dvd67 hζ s
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  let P : Ideal (𝓞 K) := Ideal.span {π}
  let M : Ideal (𝓞 K) := gcd (Ideal.span {s.omega}) (Ideal.span {s.theta})
  let Z : Ideal (𝓞 K) :=
    z_div_m (K := K) (p := 67)
      (x := s.omega) (y := s.theta) (z := s.xi)
      (ε := historicalRegularUnit67 hζ s) (m := 2 * s.m - 1)
      hζ e hy
  let root := fun η : nthRootsFinset 67 (1 : 𝓞 K) ↦
    root_div_zeta_sub_one_dvd_gcd
      (K := K) (p := 67) (x := s.omega) (y := s.theta)
      (z := s.xi) (ε := historicalRegularUnit67 hζ s)
      (m := 2 * s.m - 1) (by norm_num) hζ e hy η
  let c := fun η : nthRootsFinset 67 (1 : 𝓞 K) ↦
    div_zeta_sub_one_dvd_gcd
      (K := K) (p := 67) (x := s.omega) (y := s.theta)
      (z := s.xi) (ε := historicalRegularUnit67 hζ s)
      (m := 2 * s.m - 1) (by norm_num) hζ e hy η
  let η₀ := zeta_sub_one_dvd_root
    (K := K) (p := 67) (x := s.omega) (y := s.theta)
    (z := s.xi) (ε := historicalRegularUnit67 hζ s)
    (m := 2 * s.m - 1) (by norm_num) hζ e hy
  let Q : Ideal (𝓞 K) :=
    ∏ η ∈ Finset.attach (nthRootsFinset 67 (1 : 𝓞 K)) \ {η₀}, root η
  have hM : M = 1 := by
    have hcop :
        IsCoprime (Ideal.span {s.omega}) (Ideal.span {s.theta}) :=
      (Ideal.isCoprime_span_singleton_iff _ _).mpr
        s.coprime_omega_theta
    simpa only [M] using (Ideal.isCoprime_iff_gcd.mp hcop)
  have hZ : Z = Ideal.span {s.xi} := by
    have hzspec :
        Ideal.span {s.xi} = M * Z := by
      simpa only [M, Z] using
        (z_div_m_spec (K := K) (p := 67)
          (x := s.omega) (y := s.theta) (z := s.xi)
          (ε := historicalRegularUnit67 hζ s)
          (m := 2 * s.m - 1) hζ e hy)
    rw [hM, one_mul] at hzspec
    exact hzspec.symm
  have hrootpow (η : nthRootsFinset 67 (1 : 𝓞 K)) :
      root η ^ 67 = c η := by
    simpa only [root, c] using
      (root_div_zeta_sub_one_dvd_gcd_spec
        (K := K) (p := 67) (x := s.omega) (y := s.theta)
        (z := s.xi) (ε := historicalRegularUnit67 hζ s)
        (m := 2 * s.m - 1) (by norm_num) hζ e hy η)
  have hprodC :
      ∏ η ∈ Finset.attach (nthRootsFinset 67 (1 : 𝓞 K)), c η =
        (Z * P ^ (2 * s.m - 1)) ^ 67 := by
    simpa only [c, Z, P, π] using
      (prod_c (K := K) (p := 67)
        (x := s.omega) (y := s.theta) (z := s.xi)
        (ε := historicalRegularUnit67 hζ s)
        (m := 2 * s.m - 1) (by norm_num) hζ e hy)
  have hprodRootPow :
      (∏ η ∈ Finset.attach (nthRootsFinset 67 (1 : 𝓞 K)),
          root η) ^ 67 =
        (Z * P ^ (2 * s.m - 1)) ^ 67 := by
    rw [← Finset.prod_pow]
    simpa only [hrootpow] using hprodC
  have hprodRoot :
      ∏ η ∈ Finset.attach (nthRootsFinset 67 (1 : 𝓞 K)), root η =
        Z * P ^ (2 * s.m - 1) :=
    pow_left_injective (M := Ideal (𝓞 K))
      (by norm_num : 67 ≠ 0) hprodRootPow
  have hη₀one :
      η₀ = oneNthRoot (K := K) (p := 67) := by
    simpa only [η₀, e, hy] using
      distinguishedRoot_eq_one_of_real67 hζ e hy hs.1 hs.2.1
  have hrootη₀ :
      root η₀ = historicalOneFactorIdeal67 hζ s := by
    rw [hη₀one]
    rfl
  have hsplit :
      root η₀ * Q = Z * P ^ (2 * s.m - 1) := by
    rw [← hprodRoot]
    dsimp only [Q]
    exact (Finset.prod_eq_mul_prod_diff_singleton_of_mem
      (Finset.mem_attach _ η₀) root).symm
  have hspec :
      P ^ (2 * s.m - 1) *
          historicalEquationEightAIdeal67 hζ s =
        root η₀ := by
    rw [hrootη₀]
    simpa only [P, π] using
      historicalEquationEightAIdeal_spec67 hζ s hs
  have hP0 : P ^ (2 * s.m - 1) ≠ 0 := by
    apply pow_ne_zero
    dsimp [P, π]
    simpa only [Ideal.zero_eq_bot, ne_eq,
      Ideal.span_singleton_eq_bot] using
      hζ.unit'_coe.sub_one_ne_zero (by norm_num)
  have hfactor :
      Ideal.span {s.xi} =
        historicalEquationEightAIdeal67 hζ s * Q := by
    apply mul_left_cancel₀ hP0
    symm
    calc
      P ^ (2 * s.m - 1) *
          (historicalEquationEightAIdeal67 hζ s * Q) =
          (P ^ (2 * s.m - 1) *
            historicalEquationEightAIdeal67 hζ s) * Q := by
              rw [mul_assoc]
      _ = root η₀ * Q := by rw [hspec]
      _ = Z * P ^ (2 * s.m - 1) := hsplit
      _ = P ^ (2 * s.m - 1) * Ideal.span {s.xi} := by
        rw [hZ]
        ac_rfl
  have hcop :
      IsCoprime (historicalEquationEightAIdeal67 hζ s) Q := by
    apply IsCoprime.prod_right
    intro η hη
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hη
    have hc :
        IsCoprime (c η₀) (c η) := by
      exact coprime_c (K := K) (p := 67)
        (x := s.omega) (y := s.theta) (z := s.xi)
        (ε := historicalRegularUnit67 hζ s)
        (m := 2 * s.m - 1) (by norm_num) hζ e hy
        η₀ η (Ne.symm hη.2)
    rw [← hrootpow η₀, ← hrootpow η] at hc
    have hroots : IsCoprime (root η₀) (root η) :=
      (IsCoprime.pow_left_iff (by norm_num : 0 < 67)).mp
        ((IsCoprime.pow_right_iff (by norm_num : 0 < 67)).mp hc)
    rw [← hspec] at hroots
    exact hroots.of_mul_left_right
  simpa only [historicalEquationEightAComplement67, e, hy, root, η₀, Q] using
    And.intro hfactor hcop

set_option maxRecDepth 4000 in
theorem historicalEquationEightAComplement_ne_top67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (s : HistoricalState hζ) (hs : RealSourceAdmissible hζ s) :
    historicalEquationEightAComplement67 hζ s ≠ ⊤ := by
  classical
  intro hQtop
  let e := historicalState_regularEquation67 hζ s
  let hy := historicalState_theta_not_dvd67 hζ s
  let π : 𝓞 K := (hζ.unit' : 𝓞 K) - 1
  let root := fun η : nthRootsFinset 67 (1 : 𝓞 K) ↦
    root_div_zeta_sub_one_dvd_gcd
      (K := K) (p := 67) (x := s.omega) (y := s.theta)
      (z := s.xi) (ε := historicalRegularUnit67 hζ s)
      (m := 2 * s.m - 1) (by norm_num) hζ e hy η
  let η₀ := zeta_sub_one_dvd_root
    (K := K) (p := 67) (x := s.omega) (y := s.theta)
    (z := s.xi) (ε := historicalRegularUnit67 hζ s)
    (m := 2 * s.m - 1) (by norm_num) hζ e hy
  let ηζ : nthRootsFinset 67 (1 : 𝓞 K) :=
    zetaNthRoot (K := K) (p := 67) hζ
  have hη₀one :
      η₀ = oneNthRoot (K := K) (p := 67) := by
    simpa only [η₀, e, hy] using
      distinguishedRoot_eq_one_of_real67 hζ e hy hs.1 hs.2.1
  have hηζ_ne : ηζ ≠ η₀ := by
    rw [hη₀one]
    intro h
    have hv := congrArg
      (fun x : nthRootsFinset 67 (1 : 𝓞 K) ↦ (x : 𝓞 K)) h
    exact hζ.unit'_coe.ne_one (by norm_num) hv
  have hηζmem :
      ηζ ∈
        Finset.attach (nthRootsFinset 67 (1 : 𝓞 K)) \ {η₀} := by
    simp only [Finset.mem_sdiff, Finset.mem_attach,
      Finset.mem_singleton, true_and]
    exact hηζ_ne
  have hrootDvd :
      root ηζ ∣ historicalEquationEightAComplement67 hζ s := by
    simpa only [historicalEquationEightAComplement67, e, hy, root, η₀] using
      (Finset.dvd_prod_of_mem root hηζmem)
  have hrootUnit : IsUnit (root ηζ) := by
    apply isUnit_of_dvd_one
    simpa only [hQtop, Ideal.one_eq_top] using hrootDvd
  have hrootTop : root ηζ = ⊤ := by
    simpa only [Ideal.isUnit_iff] using hrootUnit
  have hfactorIdealTop :
      historicalZetaFactorIdeal67 hζ s = ⊤ := by
    simpa only [root, ηζ, historicalZetaFactorIdeal67] using hrootTop
  have hqspan :
      Ideal.span {historicalZetaFactor67 hζ s} = ⊤ := by
    rw [← historicalZetaFactorIdeal_pow67 hζ s, hfactorIdealTop]
    simp
  have hqunit :
      IsUnit (historicalZetaFactor67 hζ s) :=
    Ideal.span_singleton_eq_top.mp hqspan
  let qUnit : (𝓞 K)ˣ := hqunit.unit
  let A : (𝓞 K)ˣ := -qUnit
  let B : (𝓞 K)ˣ := NumberField.IsCMField.unitsComplexConj K A
  have hqUnitVal :
      (qUnit : 𝓞 K) = historicalZetaFactor67 hζ s :=
    hqunit.unit_spec
  have hAval :
      (A : 𝓞 K) = -historicalZetaFactor67 hζ s := by
    dsimp [A]
    exact congrArg Neg.neg hqUnitVal
  have hone :
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
        (1 - (hζ.unit' : 𝓞 K)) * (A : 𝓞 K) := by
    have hqmul :
        historicalZetaFactor67 hζ s * π =
          s.omega + s.theta * (hζ.unit' : 𝓞 K) :=
      div_zeta_sub_one_mul_zeta_sub_one
        (by norm_num : 67 ≠ 2) hζ
        (historicalState_regularEquation67 hζ s)
        (zetaNthRoot (K := K) (p := 67) hζ)
    dsimp [π] at hqmul
    calc
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
          s.omega + s.theta * (hζ.unit' : 𝓞 K) := by ring
      _ = historicalZetaFactor67 hζ s *
          ((hζ.unit' : 𝓞 K) - 1) := hqmul.symm
      _ = (1 - (hζ.unit' : 𝓞 K)) * (A : 𝓞 K) := by
        rw [hAval]
        ring
  have hconjζ :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (hζ.unit' : 𝓞 K) =
        (hζ.unit'⁻¹ : (𝓞 K)ˣ) :=
    congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K)
      (unitsComplexConj_zeta67 hζ)
  have hBval :
      (B : 𝓞 K) =
        NumberField.IsCMField.ringOfIntegersComplexConj K (A : 𝓞 K) :=
    rfl
  have hminus :
      s.omega + (hζ.unit'⁻¹ : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit'⁻¹ : (𝓞 K)ˣ)) * (B : 𝓞 K) := by
    have hc := congrArg
      (NumberField.IsCMField.ringOfIntegersComplexConj K) hone
    simpa only [map_add, map_mul, map_sub, map_one,
      hs.1, hs.2.1, hconjζ, hBval] using hc
  obtain ⟨j, hj⟩ :=
    unit_inv_conj_is_root_of_unity hζ A (by norm_num)
  let r : (𝓞 K)ˣ := (hζ.unit' ^ j) ^ 2
  have hAB : A = r * B := by
    calc
      A = (A * B⁻¹) * B := by simp
      _ = r * B := by simpa only [B, r] using congrArg (· * B) hj
  have hABval : (A : 𝓞 K) = (r : 𝓞 K) * (B : 𝓞 K) :=
    congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hAB
  have hzinv :
      (hζ.unit' : 𝓞 K) *
          (hζ.unit'⁻¹ : (𝓞 K)ˣ) = 1 := by
    rw [← Units.val_mul]
    simp
  have hminusZ :
      (hζ.unit' : 𝓞 K) * s.omega + s.theta =
        -(1 - (hζ.unit' : 𝓞 K)) * (B : 𝓞 K) := by
    calc
      (hζ.unit' : 𝓞 K) * s.omega + s.theta =
          (hζ.unit' : 𝓞 K) *
            (s.omega +
              (hζ.unit'⁻¹ : (𝓞 K)ˣ) * s.theta) := by
        rw [mul_add, ← mul_assoc, hzinv, one_mul]
      _ = (hζ.unit' : 𝓞 K) *
          ((1 - (hζ.unit'⁻¹ : (𝓞 K)ˣ)) * (B : 𝓞 K)) := by
            rw [hminus]
      _ = -(1 - (hζ.unit' : 𝓞 K)) * (B : 𝓞 K) := by
        calc
          _ = ((hζ.unit' : 𝓞 K) -
              (hζ.unit' : 𝓞 K) *
                (hζ.unit'⁻¹ : (𝓞 K)ˣ)) * (B : 𝓞 K) := by ring
          _ = ((hζ.unit' : 𝓞 K) - 1) * (B : 𝓞 K) := by
            rw [hzinv]
          _ = _ := by ring
  have honeR :
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
        (1 - (hζ.unit' : 𝓞 K)) *
          ((r : 𝓞 K) * (B : 𝓞 K)) := by
    rw [← hABval]
    exact hone
  have hsum :
      (1 + (hζ.unit' : 𝓞 K)) * (s.omega + s.theta) =
        (1 - (hζ.unit' : 𝓞 K)) *
          ((r : 𝓞 K) - 1) * (B : 𝓞 K) := by
    linear_combination honeR + hminusZ
  have hidentity :
      (1 - (r : 𝓞 K)) *
          (1 - (hζ.unit' : 𝓞 K)) * (B : 𝓞 K) =
        -(1 + (hζ.unit' : 𝓞 K)) * (s.omega + s.theta) := by
    calc
      _ = -((1 - (hζ.unit' : 𝓞 K)) *
          ((r : 𝓞 K) - 1) * (B : 𝓞 K)) := by ring
      _ = -((1 + (hζ.unit' : 𝓞 K)) *
          (s.omega + s.theta)) :=
        congrArg Neg.neg hsum.symm
      _ = -(1 + (hζ.unit' : 𝓞 K)) *
          (s.omega + s.theta) := by rw [neg_mul]
  have hr_ne : (r : 𝓞 K) ≠ 1 := by
    intro hr
    have hzero :
        (1 + (hζ.unit' : 𝓞 K)) *
          (s.omega + s.theta) = 0 := by
      have := hidentity
      rw [hr] at this
      linear_combination this
    have hplusUnit :
        IsUnit ((1 : 𝓞 K) + hζ.unit') := by
      simpa [add_comm] using
        hζ.unit'_coe.geom_sum_isUnit (by norm_num)
          (by norm_num : Nat.Coprime 2 67)
    exact historicalState_omega_add_theta_ne_zero67 hζ s
      ((mul_eq_zero.mp hzero).resolve_left hplusUnit.ne_zero)
  have h67sum : (67 : 𝓞 K) ∣ s.omega + s.theta := by
    have h60 :=
      historicalState_omega_add_theta_highDivisibility67 hζ s hs
    have h58 :
        π ^ 66 ∣ s.omega + s.theta :=
      (pow_dvd_pow π (by norm_num : 66 ≤ 68)).trans
        (by simpa only [π] using h60)
    exact ((associated_zeta_sub_one_pow_prime hζ).dvd_iff_dvd_left).mp
      (by simpa only [π] using h58)
  have h67prod :
      (67 : 𝓞 K) ∣
        (1 - (r : 𝓞 K)) *
          (1 - (hζ.unit' : 𝓞 K)) := by
    have hwithB :
        (67 : 𝓞 K) ∣
          ((1 - (r : 𝓞 K)) *
            (1 - (hζ.unit' : 𝓞 K))) * (B : 𝓞 K) := by
      rw [hidentity]
      exact dvd_mul_of_dvd_right h67sum _
    exact (B.isUnit.dvd_mul_right).mp hwithB
  have hrpow : (r : 𝓞 K) ^ 67 = 1 := by
    change ((((hζ.unit' : 𝓞 K) ^ j) ^ 2) ^ 67) = 1
    rw [← pow_mul, ← pow_mul]
    rw [show j * (2 * 67) = 67 * (j * 2) by omega, pow_mul,
      hζ.unit'_coe.pow_eq_one, one_pow]
  let ηr : nthRootsFinset 67 (1 : 𝓞 K) :=
    ⟨(r : 𝓞 K), by
      rw [Polynomial.mem_nthRootsFinset (by norm_num : 0 < 67)]
      exact hrpow⟩
  let ηone : nthRootsFinset 67 (1 : 𝓞 K) :=
    oneNthRoot (K := K) (p := 67)
  have hηr_ne : (ηr : 𝓞 K) ≠ (ηone : 𝓞 K) := by
    simpa only [ηr, ηone, oneNthRoot] using hr_ne
  have hrAssocSub :
      Associated ((r : 𝓞 K) - 1) π := by
    simpa only [ηr, ηone, oneNthRoot, π] using
      (hζ.unit'_coe.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
        (by norm_num : Nat.Prime 67) ηr.prop ηone.prop hηr_ne).symm
  have hrAssoc :
      Associated (1 - (r : 𝓞 K)) π := by
    have hneg :
        Associated (-((r : 𝓞 K) - 1)) ((r : 𝓞 K) - 1) := by
      simpa only [Units.val_neg, Units.val_one, neg_mul, one_mul] using
        associated_unit_mul_left
          ((r : 𝓞 K) - 1)
          ((-1 : (𝓞 K)ˣ) : 𝓞 K) (-1 : (𝓞 K)ˣ).isUnit
    simpa only [neg_sub] using hneg.trans hrAssocSub
  have hzAssoc :
      Associated (1 - (hζ.unit' : 𝓞 K)) π := by
    simpa only [π, pow_one, Units.val_one, mul_one] using
      associated_one_sub_zetaPow_mul_unit67 hζ 1
        (by norm_num) (by norm_num) (1 : (𝓞 K)ˣ)
  have hprodAssoc :
      Associated
        ((1 - (r : 𝓞 K)) * (1 - (hζ.unit' : 𝓞 K)))
        (π ^ 2) := by
    simpa only [pow_two] using hrAssoc.mul_mul hzAssoc
  have hπ58prod :
      π ^ 66 ∣
        (1 - (r : 𝓞 K)) * (1 - (hζ.unit' : 𝓞 K)) := by
    exact ((associated_zeta_sub_one_pow_prime hζ).dvd_iff_dvd_left).mpr
      (by simpa only [π] using h67prod)
  have hbad : π ^ 66 ∣ π ^ 2 :=
    (hprodAssoc.dvd_iff_dvd_right).mp hπ58prod
  have hle :
      66 ≤ 2 :=
    (pow_dvd_pow_iff
      (hζ.unit'_coe.sub_one_ne_zero (by norm_num))
      hζ.zeta_sub_one_prime'.not_unit).mp (by simpa only [π] using hbad)
  omega

/-- The historical factor allocation supplies the strict support drop for
the square of any chosen generator of equation (8a), with no residual
factorization hypotheses left to the final Vandiver assembly. -/
theorem historicalEquationEightA_square_support_strict_unconditional67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67)
    (s : HistoricalState hζ) (hs : RealSourceAdmissible hζ s)
    (ρzero : 𝓞 K)
    (hgenerator :
      historicalEquationEightAIdeal67 hζ s =
        Ideal.span {ρzero}) :
    primeIdealFactorSupport67 (ρzero ^ 2) ⊂
      primeIdealFactorSupport67 s.xi := by
  obtain ⟨hfactor, hcop⟩ :=
    historicalEquationEightA_factorization_and_coprime67 hζ s hs
  exact historicalEquationEightA_square_support_strict67
    hζ s ρzero (historicalEquationEightAComplement67 hζ s)
    hgenerator hfactor
    (historicalEquationEightAComplement_ne_top67 hζ s hs) hcop

end

end Fermat.SixtySeven.VandiverHistorical
