import Fermat.Exponents.FiftyNine.Conservation.TwistedLambdaNormCorrection59
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.Tactic

open scoped NumberField Valued
open Polynomial

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.EisensteinIntegrality59

open Fermat.Conservation.KummerCyclicQuotient59
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
open Fermat.FiftyNine.Conservation.TwistedLambdaNormCorrection59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

abbrev F59 := LambdaField59 K
abbrev E59 := twistedLambdaKummerExtension59 K

private theorem primitiveRoots59_nonempty :
    (primitiveRoots 59 (F59 K)).Nonempty := by
  refine ⟨lambdaLocalPrimitiveRoot59 K, ?_⟩
  exact (mem_primitiveRoots (by norm_num : 0 < 59)).2
    (lambdaLocalPrimitiveRoot59_isPrimitive K)

/-- The selected Kummer root generates the whole splitting field. -/
theorem adjoin_twistedLambdaRoot59_eq_top :
    Algebra.adjoin (F59 K) ({twistedLambdaRoot59 K} : Set (E59 K)) = ⊤ := by
  letI : IsSplittingField (F59 K) (E59 K)
      (kummerPolynomial59 (F59 K) (twistedLambda59 K)) :=
    kummerExtension59_isSplittingField (F59 K) (twistedLambda59 K)
  exact Algebra.adjoin_root_eq_top_of_isSplittingField
    (primitiveRoots59_nonempty K)
    (twistedLambdaPolynomial59_irreducible K)
    (twistedLambdaRoot59_pow K)

/-- The honest selected-root power basis of the twisted Kummer extension. -/
noncomputable def twistedLambdaPowerBasis59 : PowerBasis (F59 K) (E59 K) :=
  PowerBasis.ofAdjoinEqTop
    (Algebra.IsIntegral.isIntegral (R := F59 K)
      (x := twistedLambdaRoot59 K))
    (adjoin_twistedLambdaRoot59_eq_top K)

@[simp]
theorem twistedLambdaPowerBasis59_gen :
    (twistedLambdaPowerBasis59 K).gen = twistedLambdaRoot59 K :=
  rfl

theorem twistedLambdaRoot59_minpoly :
    minpoly (F59 K) (twistedLambdaRoot59 K) =
      kummerPolynomial59 (F59 K) (twistedLambda59 K) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · exact twistedLambdaPolynomial59_irreducible K
  · simp only [kummerPolynomial59, map_sub, map_pow, aeval_X, aeval_C]
    rw [twistedLambdaRoot59_pow]
    ring
  · exact monic_X_pow_sub_C _ (by norm_num : 59 ≠ 0)

@[simp]
theorem twistedLambdaPowerBasis59_dim :
    (twistedLambdaPowerBasis59 K).dim = 59 := by
  rw [twistedLambdaPowerBasis59, PowerBasis.ofAdjoinEqTop_dim,
    twistedLambdaRoot59_minpoly]
  simp [kummerPolynomial59]

noncomputable local instance twistedLambdaFiniteDimensional59 :
    FiniteDimensional (F59 K) (E59 K) :=
  (twistedLambdaPowerBasis59 K).finite

/-- The constant-coordinate index of the selected-root power basis. -/
noncomputable def twistedLambdaPowerBasis59_zeroIndex :
    Fin (twistedLambdaPowerBasis59 K).dim :=
  ⟨0, (twistedLambdaPowerBasis59 K).dim_pos⟩

@[simp]
theorem twistedLambdaPowerBasis59_zeroIndex_val :
    (twistedLambdaPowerBasis59_zeroIndex K : ℕ) = 0 :=
  rfl

/-- The base norm of the field norm is the 59th power of the unique
spectral norm on the twisted extension.  This is the valuation-extension
identity needed below, obtained without postulating an extension valuation. -/
theorem norm_algebraNorm_eq_spectralNorm_pow59 (beta : E59 K) :
    ‖Algebra.norm (F59 K) beta‖ = spectralNorm (F59 K) (E59 K) beta ^ 59 := by
  letI : IsSplittingField (F59 K) (E59 K)
      (kummerPolynomial59 (F59 K) (twistedLambda59 K)) :=
    kummerExtension59_isSplittingField (F59 K) (twistedLambda59 K)
  letI : FiniteDimensional (F59 K) (E59 K) :=
    Polynomial.IsSplittingField.finiteDimensional
      (E59 K) (kummerPolynomial59 (F59 K) (twistedLambda59 K))
  letI : IsGalois (F59 K) (E59 K) :=
    isGalois_of_isSplittingField_X_pow_sub_C
      ⟨lambdaLocalPrimitiveRoot59 K,
        (mem_primitiveRoots (by norm_num : 0 < 59)).2
          (lambdaLocalPrimitiveRoot59_isPrimitive K)⟩
      (twistedLambdaPolynomial59_irreducible K) (E59 K)
  letI : NormedField (E59 K) :=
    spectralNorm.normedField (F59 K) (E59 K)
  letI : NormedAlgebra (F59 K) (E59 K) :=
    spectralNorm.normedAlgebra (F59 K) (E59 K)
  have hcard : Fintype.card ((E59 K) ≃ₐ[F59 K] (E59 K)) = 59 := by
    rw [Fintype.card_eq_nat_card,
      IsGalois.card_aut_eq_finrank (F59 K) (E59 K)]
    calc
      Module.finrank (F59 K) (E59 K) =
          (twistedLambdaPowerBasis59 K).dim :=
        (twistedLambdaPowerBasis59 K).finrank
      _ = 59 := twistedLambdaPowerBasis59_dim K
  calc
    ‖Algebra.norm (F59 K) beta‖ =
        ‖algebraMap (F59 K) (E59 K) (Algebra.norm (F59 K) beta)‖ := by
      rw [norm_algebraMap, norm_one, mul_one]
    _ = ‖∏ σ : (E59 K) ≃ₐ[F59 K] (E59 K), σ beta‖ := by
      rw [Algebra.norm_eq_prod_automorphisms]
    _ = ∏ σ : (E59 K) ≃ₐ[F59 K] (E59 K), ‖σ beta‖ := norm_prod _ _
    _ = ∏ _σ : (E59 K) ≃ₐ[F59 K] (E59 K), ‖beta‖ := by
      apply Finset.prod_congr rfl
      intro σ hσ
      rw [NormedAlgebra.norm_eq_spectralNorm (F59 K),
        NormedAlgebra.norm_eq_spectralNorm (F59 K)]
      exact (spectralNorm_eq_of_equiv σ beta).symm
    _ = ‖beta‖ ^ 59 := by
      rw [Finset.prod_const, Finset.card_univ, hcard]
    _ = spectralNorm (F59 K) (E59 K) beta ^ 59 := by
      rw [NormedAlgebra.norm_eq_spectralNorm (F59 K)]

/-- A unit field norm forces spectral absolute value one upstairs. -/
theorem spectralNorm_eq_one_of_algebraNorm_valuation_eq_one
    (beta : E59 K)
    (hbeta : Valued.v (Algebra.norm (F59 K) beta) = 1) :
    spectralNorm (F59 K) (E59 K) beta = 1 := by
  have hnorm : ‖Algebra.norm (F59 K) beta‖ = 1 := by
    apply le_antisymm
    · rw [Valued.toNormedField.norm_le_one_iff]
      exact hbeta.le
    · rw [Valued.toNormedField.one_le_norm_iff]
      exact hbeta.ge
  have hpow : spectralNorm (F59 K) (E59 K) beta ^ 59 = 1 := by
    rw [← norm_algebraNorm_eq_spectralNorm_pow59 K beta, hnorm]
  exact (pow_eq_one_iff_of_nonneg
    (spectralNorm_nonneg beta) (by norm_num : 59 ≠ 0)).mp hpow

/-- The selected root has the expected 59th-power spectral norm. -/
theorem spectralNorm_twistedLambdaRoot59_pow59 :
    spectralNorm (F59 K) (E59 K) (twistedLambdaRoot59 K) ^ 59 =
      ‖twistedLambda59 K‖ := by
  rw [← spectralMulAlgNorm_def]
  rw [← map_pow, twistedLambdaRoot59_pow]
  exact spectralNorm_extends (twistedLambda59 K)

theorem norm_twistedLambda59_lt_one : ‖twistedLambda59 K‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff,
    twistedLambda59_valuation]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

theorem spectralNorm_twistedLambdaRoot59_lt_one :
    spectralNorm (F59 K) (E59 K) (twistedLambdaRoot59 K) < 1 := by
  rw [← pow_lt_one_iff_of_nonneg
    (spectralNorm_nonneg (twistedLambdaRoot59 K))
    (by norm_num : 59 ≠ 0)]
  rw [spectralNorm_twistedLambdaRoot59_pow59]
  exact norm_twistedLambda59_lt_one K

/-- Spectral norm of one selected-root monomial. -/
theorem spectralNorm_algebraMap_mul_root_pow
    (b : F59 K) (i : ℕ) :
    spectralNorm (F59 K) (E59 K)
        (algebraMap (F59 K) (E59 K) b * twistedLambdaRoot59 K ^ i) =
      ‖b‖ * spectralNorm (F59 K) (E59 K) (twistedLambdaRoot59 K) ^ i := by
  rw [← spectralMulAlgNorm_def]
  rw [map_mul, map_pow]
  simp only [spectralMulAlgNorm_def, spectralNorm_extends]

/-- Equality of two weighted monomial norms gives equality of the
corresponding base-field norm expressions after taking 59th powers. -/
theorem norm_weight_eq_of_spectral_monomial_norm_eq
    {b c : F59 K} {i j : ℕ}
    (h : spectralNorm (F59 K) (E59 K)
          (algebraMap (F59 K) (E59 K) b * twistedLambdaRoot59 K ^ i) =
        spectralNorm (F59 K) (E59 K)
          (algebraMap (F59 K) (E59 K) c * twistedLambdaRoot59 K ^ j)) :
    ‖b ^ 59 * twistedLambda59 K ^ i‖ =
      ‖c ^ 59 * twistedLambda59 K ^ j‖ := by
  rw [spectralNorm_algebraMap_mul_root_pow,
    spectralNorm_algebraMap_mul_root_pow] at h
  have hp := congrArg (fun x : ℝ ↦ x ^ 59) h
  have hroot_i :
      (spectralNorm (F59 K) (E59 K) (twistedLambdaRoot59 K) ^ i) ^ 59 =
        ‖twistedLambda59 K‖ ^ i := by
    rw [← pow_mul, pow_mul', spectralNorm_twistedLambdaRoot59_pow59]
  have hroot_j :
      (spectralNorm (F59 K) (E59 K) (twistedLambdaRoot59 K) ^ j) ^ 59 =
        ‖twistedLambda59 K‖ ^ j := by
    rw [← pow_mul, pow_mul', spectralNorm_twistedLambdaRoot59_pow59]
  simpa only [mul_pow, norm_mul, norm_pow, hroot_i, hroot_j] using hp

/-- Distinct exponents below 59 have distinct weights.  This is the
Eisenstein/no-cancellation fact at the heart of the selected-root basis. -/
theorem spectral_monomial_norm_ne_of_ne
    {b c : F59 K} (hb : b ≠ 0) (hc : c ≠ 0)
    {i j : ℕ} (hi : i < 59) (hj : j < 59) (hij : i ≠ j) :
    spectralNorm (F59 K) (E59 K)
        (algebraMap (F59 K) (E59 K) b * twistedLambdaRoot59 K ^ i) ≠
      spectralNorm (F59 K) (E59 K)
        (algebraMap (F59 K) (E59 K) c * twistedLambdaRoot59 K ^ j) := by
  intro h
  have hnorm := norm_weight_eq_of_spectral_monomial_norm_eq K h
  have hval :
      Valued.v (b ^ 59 * twistedLambda59 K ^ i) =
        Valued.v (c ^ 59 * twistedLambda59 K ^ j) := by
    apply le_antisymm
    · rw [← Valued.toNormedField.norm_le_iff]
      exact hnorm.le
    · rw [← Valued.toNormedField.norm_le_iff]
      exact hnorm.ge
  simp only [map_mul, map_pow, twistedLambda59_valuation] at hval
  have hbval0 : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  have hcval0 : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  have hexp0 : WithZero.exp (-1 : ℤ) ≠ 0 := WithZero.exp_ne_zero
  have hlog := congrArg
    (fun x : WithZero (Multiplicative ℤ) ↦ WithZero.log x) hval
  rw [WithZero.log_mul (pow_ne_zero _ hbval0) (pow_ne_zero _ hexp0),
    WithZero.log_mul (pow_ne_zero _ hcval0) (pow_ne_zero _ hexp0),
    WithZero.log_pow, WithZero.log_pow, WithZero.log_pow,
    WithZero.log_pow, WithZero.log_exp] at hlog
  simp only [nsmul_eq_mul] at hlog
  omega

/-- A weighted monomial lying in the spectral unit ball has an integral
base coefficient.  The key discrete step is that an exponent `i < 59`
cannot compensate even one negative base valuation, whose ramification
weight is 59. -/
theorem coefficient_valuation_le_one_of_weighted_norm_le_one
    (b : F59 K) {i : ℕ} (hi : i < 59)
    (hweight : spectralNorm (F59 K) (E59 K)
        (algebraMap (F59 K) (E59 K) b * twistedLambdaRoot59 K ^ i) ≤ 1) :
    Valued.v b ≤ 1 := by
  by_cases hb : b = 0
  · simp [hb]
  by_contra hnot
  have hbval0 : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  have hbgt : 1 < Valued.v b := lt_of_not_ge hnot
  have hlogb : (0 : ℤ) < WithZero.log (Valued.v b) := by
    have := (WithZero.log_lt_log one_ne_zero hbval0).2 hbgt
    simpa using this
  have hprod0 :
      Valued.v (b ^ 59 * twistedLambda59 K ^ i) ≠ 0 := by
    apply (Valuation.ne_zero_iff _).2
    exact mul_ne_zero (pow_ne_zero _ hb)
      (pow_ne_zero _ (by
        intro ha
        have hval := twistedLambda59_valuation K
        rw [ha, map_zero] at hval
        exact WithZero.exp_ne_zero hval.symm))
  have hvalprod :
      1 < Valued.v (b ^ 59 * twistedLambda59 K ^ i) := by
    apply (WithZero.log_lt_log one_ne_zero hprod0).mp
    have hbpow0 : Valued.v b ^ 59 ≠ 0 := pow_ne_zero _ hbval0
    have hexppow0 : WithZero.exp (-1 : ℤ) ^ i ≠ 0 :=
      pow_ne_zero _ WithZero.exp_ne_zero
    rw [WithZero.log_one, map_mul, map_pow, map_pow,
      twistedLambda59_valuation,
      WithZero.log_mul hbpow0 hexppow0,
      WithZero.log_pow, WithZero.log_pow, WithZero.log_exp]
    simp only [nsmul_eq_mul]
    omega
  have hnormprod : 1 < ‖b ^ 59 * twistedLambda59 K ^ i‖ := by
    rw [Valued.toNormedField.one_lt_norm_iff]
    exact hvalprod
  have hpow :
      spectralNorm (F59 K) (E59 K)
          (algebraMap (F59 K) (E59 K) b * twistedLambdaRoot59 K ^ i) ^ 59 =
        ‖b ^ 59 * twistedLambda59 K ^ i‖ := by
    rw [spectralNorm_algebraMap_mul_root_pow]
    have hroot_i :
        (spectralNorm (F59 K) (E59 K) (twistedLambdaRoot59 K) ^ i) ^ 59 =
          ‖twistedLambda59 K‖ ^ i := by
      rw [← pow_mul, pow_mul', spectralNorm_twistedLambdaRoot59_pow59]
    simp only [mul_pow, norm_mul, norm_pow, hroot_i]
  have hone : 1 < spectralNorm (F59 K) (E59 K)
      (algebraMap (F59 K) (E59 K) b * twistedLambdaRoot59 K ^ i) := by
    rw [← one_lt_pow_iff_of_nonneg
      (spectralNorm_nonneg _) (by norm_num : 59 ≠ 0)]
    rw [hpow]
    exact hnormprod
  exact (not_lt_of_ge hweight) hone

/-- Every nonzero element has a unique dominant selected-root coordinate,
and its spectral norm is exactly that coordinate's weighted norm. -/
theorem exists_dominant_twistedLambdaPowerBasis_coefficient
    (beta : E59 K) (hbeta : beta ≠ 0) :
    ∃ k : Fin (twistedLambdaPowerBasis59 K).dim,
      (twistedLambdaPowerBasis59 K).basis.repr beta k ≠ 0 ∧
      spectralNorm (F59 K) (E59 K) beta =
        ‖(twistedLambdaPowerBasis59 K).basis.repr beta k‖ *
          spectralNorm (F59 K) (E59 K) (twistedLambdaRoot59 K) ^ (k : ℕ) ∧
      ∀ i : Fin (twistedLambdaPowerBasis59 K).dim,
        spectralNorm (F59 K) (E59 K)
            (algebraMap (F59 K) (E59 K)
                ((twistedLambdaPowerBasis59 K).basis.repr beta i) *
              twistedLambdaRoot59 K ^ (i : ℕ)) ≤
          spectralNorm (F59 K) (E59 K) beta := by
  let B := twistedLambdaPowerBasis59 K
  let coeff : Fin B.dim → F59 K := fun i ↦ B.basis.repr beta i
  let term : Fin B.dim → E59 K := fun i ↦
    algebraMap (F59 K) (E59 K) (coeff i) * twistedLambdaRoot59 K ^ (i : ℕ)
  have hrepr : B.basis.repr beta ≠ 0 := by
    intro hzero
    apply hbeta
    apply B.basis.repr.injective
    simpa using hzero
  have hsupp : (B.basis.repr beta).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr hrepr
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image
    (B.basis.repr beta).support
    (fun i ↦ spectralNorm (F59 K) (E59 K) (term i)) hsupp
  have hkcoeff : coeff k ≠ 0 := by
    simpa [coeff, Finsupp.mem_support_iff] using hk
  have hroot : twistedLambdaRoot59 K ≠ 0 := by
    have hlambda : twistedLambda59 K ≠ 0 := by
      have hv : Valued.v (twistedLambda59 K) ≠ 0 := by
        rw [twistedLambda59_valuation]
        exact WithZero.exp_ne_zero
      exact (Valuation.ne_zero_iff Valued.v).mp hv
    have hmap :
        algebraMap (F59 K) (E59 K) (twistedLambda59 K) ≠ 0 := by
      simpa using
        ((algebraMap (F59 K) (E59 K)).injective.ne hlambda)
    intro hzero
    have hpow := twistedLambdaRoot59_pow K
    rw [hzero, zero_pow (by norm_num : 59 ≠ 0)] at hpow
    exact hmap hpow.symm
  have hkterm : term k ≠ 0 := by
    exact mul_ne_zero
      (by simpa using
        ((algebraMap (F59 K) (E59 K)).injective.ne hkcoeff))
      (pow_ne_zero _ hroot)
  have hsum :
      spectralNorm (F59 K) (E59 K) (∑ i, term i) =
        spectralNorm (F59 K) (E59 K) (term k) := by
    change spectralAlgNorm (F59 K) (E59 K) (∑ i, term i) =
      spectralAlgNorm (F59 K) (E59 K) (term k)
    apply IsNonarchimedean.apply_sum_eq_of_lt
      isNonarchimedean_spectralNorm (Finset.mem_univ k)
    intro j hj hjk
    by_cases hjcoeff : coeff j = 0
    · have hjterm : term j = 0 := by simp [term, hjcoeff]
      rw [hjterm, map_zero]
      exact spectralNorm_zero_lt hkterm
        (Algebra.IsAlgebraic.isAlgebraic (term k))
    · have hjmem : j ∈ (B.basis.repr beta).support := by
        simpa [coeff, Finsupp.mem_support_iff] using hjcoeff
      have hle := hkmax j hjmem
      apply lt_of_le_of_ne hle
      intro heq
      apply spectral_monomial_norm_ne_of_ne K hjcoeff hkcoeff
        (by
          rw [← twistedLambdaPowerBasis59_dim K]
          exact j.isLt)
        (by
          rw [← twistedLambdaPowerBasis59_dim K]
          exact k.isLt)
        (fun hval ↦ hjk (Fin.ext hval))
      simpa [term] using heq
  have hreprsum := B.basis.sum_repr beta
  have hsumterm : (∑ i, term i) = beta := by
    rw [← hreprsum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [B.basis_eq_pow]
    simp only [term, coeff, B, twistedLambdaPowerBasis59_gen,
      Algebra.smul_def]
  have hbetaeq :
      spectralNorm (F59 K) (E59 K) beta =
        ‖coeff k‖ * spectralNorm (F59 K) (E59 K)
          (twistedLambdaRoot59 K) ^ (k : ℕ) := by
    calc
      spectralNorm (F59 K) (E59 K) beta =
          spectralNorm (F59 K) (E59 K) (∑ i, term i) := by
        rw [hsumterm]
      _ = spectralNorm (F59 K) (E59 K) (term k) := hsum
      _ = ‖coeff k‖ * spectralNorm (F59 K) (E59 K)
          (twistedLambdaRoot59 K) ^ (k : ℕ) := by
        simpa [term] using
          spectralNorm_algebraMap_mul_root_pow K (coeff k) (k : ℕ)
  refine ⟨k, hkcoeff, hbetaeq, ?_⟩
  intro i
  change spectralNorm (F59 K) (E59 K) (term i) ≤
    spectralNorm (F59 K) (E59 K) beta
  by_cases hicoeff : coeff i = 0
  · have hiterm : term i = 0 := by simp [term, hicoeff]
    rw [hiterm, spectralNorm_zero]
    exact spectralNorm_nonneg beta
  · have himem : i ∈ (B.basis.repr beta).support := by
      simpa [coeff, Finsupp.mem_support_iff] using hicoeff
    exact (hkmax i himem).trans_eq (hsumterm ▸ hsum).symm

/-- If the field norm is a base unit, every selected-root power-basis
coordinate lies in the base valuation ring. -/
theorem twistedLambdaPowerBasis59_coeff_valuation_le_one_of_norm_unit
    (beta : E59 K)
    (hbeta : Valued.v (Algebra.norm (F59 K) beta) = 1)
    (i : Fin (twistedLambdaPowerBasis59 K).dim) :
    Valued.v ((twistedLambdaPowerBasis59 K).basis.repr beta i) ≤ 1 := by
  have hbetane : beta ≠ 0 := by
    intro hzero
    subst beta
    rw [Algebra.norm_zero, map_zero] at hbeta
    exact zero_ne_one hbeta
  obtain ⟨k, hk, hkvalue, hbound⟩ :=
    exists_dominant_twistedLambdaPowerBasis_coefficient K beta hbetane
  apply coefficient_valuation_le_one_of_weighted_norm_le_one K
    ((twistedLambdaPowerBasis59 K).basis.repr beta i)
  · rw [← twistedLambdaPowerBasis59_dim K]
    exact i.isLt
  · rw [← spectralNorm_eq_one_of_algebraNorm_valuation_eq_one K beta hbeta]
    exact hbound i

/-- Under the same unit-norm hypothesis, the constant selected-root
coordinate is itself a base unit.  All positive powers of the Eisenstein
root have spectral norm strictly below one, so the dominant coordinate is
forced to be index zero. -/
theorem twistedLambdaPowerBasis59_coeff_zero_valuation_eq_one_of_norm_unit
    (beta : E59 K)
    (hbeta : Valued.v (Algebra.norm (F59 K) beta) = 1) :
    Valued.v ((twistedLambdaPowerBasis59 K).basis.repr beta
      (twistedLambdaPowerBasis59_zeroIndex K)) = 1 := by
  have hbetane : beta ≠ 0 := by
    intro hzero
    subst beta
    rw [Algebra.norm_zero, map_zero] at hbeta
    exact zero_ne_one hbeta
  obtain ⟨k, hkcoeff, hkvalue, hbound⟩ :=
    exists_dominant_twistedLambdaPowerBasis_coefficient K beta hbetane
  have hspectral : spectralNorm (F59 K) (E59 K) beta = 1 :=
    spectralNorm_eq_one_of_algebraNorm_valuation_eq_one K beta hbeta
  have hkcoeffVal :
      Valued.v ((twistedLambdaPowerBasis59 K).basis.repr beta k) ≤ 1 :=
    twistedLambdaPowerBasis59_coeff_valuation_le_one_of_norm_unit K beta hbeta k
  have hkcoeffNorm :
      ‖(twistedLambdaPowerBasis59 K).basis.repr beta k‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    exact hkcoeffVal
  have hkzeroNat : (k : ℕ) = 0 := by
    by_contra hkne
    have hrpowlt :
        spectralNorm (F59 K) (E59 K) (twistedLambdaRoot59 K) ^ (k : ℕ) < 1 :=
      pow_lt_one₀
        (spectralNorm_nonneg (twistedLambdaRoot59 K))
        (spectralNorm_twistedLambdaRoot59_lt_one K) hkne
    have hprodlt :
        ‖(twistedLambdaPowerBasis59 K).basis.repr beta k‖ *
            spectralNorm (F59 K) (E59 K) (twistedLambdaRoot59 K) ^ (k : ℕ) < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_right hkcoeffNorm
        (pow_nonneg (spectralNorm_nonneg _) _) hrpowlt
    rw [hspectral] at hkvalue
    exact (ne_of_lt hprodlt) hkvalue.symm
  have hkzero : k = twistedLambdaPowerBasis59_zeroIndex K := by
    apply Fin.ext
    simpa using hkzeroNat
  subst k
  have hnorm0 :
      ‖(twistedLambdaPowerBasis59 K).basis.repr beta
        (twistedLambdaPowerBasis59_zeroIndex K)‖ = 1 := by
    rw [hspectral] at hkvalue
    simpa using hkvalue.symm
  apply le_antisymm
  · rw [← Valued.toNormedField.norm_le_one_iff, hnorm0]
  · rw [← Valued.toNormedField.one_le_norm_iff, hnorm0]

/-- The canonical degree-`< 59` polynomial carrying the selected-root
power-basis coordinates of an extension element. -/
noncomputable def twistedLambdaPowerBasisPolynomial59 (beta : E59 K) :
    (F59 K)[X] :=
  ∑ i : Fin (twistedLambdaPowerBasis59 K).dim,
    monomial (i : ℕ) ((twistedLambdaPowerBasis59 K).basis.repr beta i)

theorem twistedLambdaPowerBasisPolynomial59_coeff
    (beta : E59 K) (n : ℕ)
    (hn : n < (twistedLambdaPowerBasis59 K).dim) :
    (twistedLambdaPowerBasisPolynomial59 K beta).coeff n =
      (twistedLambdaPowerBasis59 K).basis.repr beta ⟨n, hn⟩ := by
  rw [twistedLambdaPowerBasisPolynomial59]
  change (lcoeff (F59 K) n)
      (∑ i : Fin (twistedLambdaPowerBasis59 K).dim,
        monomial (i : ℕ)
          ((twistedLambdaPowerBasis59 K).basis.repr beta i)) = _
  rw [map_sum]
  simp only [lcoeff_apply, coeff_monomial]
  rw [Finset.sum_eq_single ⟨n, hn⟩]
  · simp
  · intro b hb hbn
    rw [if_neg]
    exact fun hval ↦ hbn (Fin.ext hval)
  · simp

theorem twistedLambdaPowerBasisPolynomial59_natDegree_lt
    (beta : E59 K) :
    (twistedLambdaPowerBasisPolynomial59 K beta).natDegree < 59 := by
  rw [twistedLambdaPowerBasisPolynomial59]
  apply lt_of_le_of_lt
    (natDegree_sum_le_of_forall_le _ _ (n := 58) ?_)
  · norm_num
  · intro i hi
    exact (natDegree_monomial_le _).trans (by
      have hil : (i : ℕ) < 59 := by
        rw [← twistedLambdaPowerBasis59_dim K]
        exact i.isLt
      omega)

theorem aeval_twistedLambdaPowerBasisPolynomial59
    (beta : E59 K) :
    aeval (twistedLambdaRoot59 K)
        (twistedLambdaPowerBasisPolynomial59 K beta) = beta := by
  calc
    aeval (twistedLambdaRoot59 K)
        (twistedLambdaPowerBasisPolynomial59 K beta) =
        ∑ i : Fin (twistedLambdaPowerBasis59 K).dim,
          aeval (twistedLambdaRoot59 K)
            (monomial (i : ℕ)
              ((twistedLambdaPowerBasis59 K).basis.repr beta i)) := by
      rw [twistedLambdaPowerBasisPolynomial59, map_sum]
    _ = ∑ i : Fin (twistedLambdaPowerBasis59 K).dim,
          ((twistedLambdaPowerBasis59 K).basis.repr beta i) •
            (twistedLambdaPowerBasis59 K).basis i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(twistedLambdaPowerBasis59 K).basis_eq_pow]
      simp only [aeval_monomial, twistedLambdaPowerBasis59_gen,
        Algebra.smul_def]
    _ = beta := (twistedLambdaPowerBasis59 K).basis.sum_repr beta

/-- Requested bounded-polynomial interface: a unit-norm extension element
has a degree-`< 59` selected-root expansion with all coefficients integral
and constant coefficient a unit. -/
theorem exists_integral_bounded_aeval_of_norm_valuation_eq_one
    (beta : E59 K)
    (hbeta : Valued.v (Algebra.norm (F59 K) beta) = 1) :
    ∃ f : (F59 K)[X],
      f.natDegree < 59 ∧
      beta = aeval (twistedLambdaRoot59 K) f ∧
      (∀ i : ℕ, i < 59 → Valued.v (f.coeff i) ≤ 1) ∧
      Valued.v (f.coeff 0) = 1 := by
  refine ⟨twistedLambdaPowerBasisPolynomial59 K beta,
    twistedLambdaPowerBasisPolynomial59_natDegree_lt K beta,
    (aeval_twistedLambdaPowerBasisPolynomial59 K beta).symm, ?_, ?_⟩
  · intro i hi
    have hidim : i < (twistedLambdaPowerBasis59 K).dim := by
      rw [twistedLambdaPowerBasis59_dim]
      exact hi
    rw [twistedLambdaPowerBasisPolynomial59_coeff K beta i hidim]
    exact twistedLambdaPowerBasis59_coeff_valuation_le_one_of_norm_unit
      K beta hbeta ⟨i, hidim⟩
  · have hzero : 0 < (twistedLambdaPowerBasis59 K).dim :=
      (twistedLambdaPowerBasis59 K).dim_pos
    rw [twistedLambdaPowerBasisPolynomial59_coeff K beta 0 hzero]
    simpa [twistedLambdaPowerBasis59_zeroIndex] using
      twistedLambdaPowerBasis59_coeff_zero_valuation_eq_one_of_norm_unit
        K beta hbeta

end Fermat.FiftyNine.Conservation.EisensteinIntegrality59
