import Fermat.Irregular.CyclotomicDirichlet37
import Mathlib.Analysis.Complex.AbelLimit

/-!
# Boundary logarithm series and the exponent-37 L-value bridge

This file proves the analytic part of the chord calculation that does not depend on analytic
continuation of Dirichlet series at their boundary.  Dirichlet's test and Abel's limit theorem
give the naturally ordered identity

  sum z^n / n = -log (1 - z)

for every unit-modulus complex number other than one.  Pairing inverse roots turns the complex
logarithms into the real chord logarithms, and a finite Fourier transform contributes exactly the
inverse-character Gauss sum.

Consequently, ChordLogLValueFormula37 follows from the single remaining proposition
DirichletSeriesAtOneFormula37: natural-order convergence of the relevant primitive Dirichlet
series to Mathlib's analytically continued LFunction value at one.  The subsequent module
`CyclotomicSeriesAtOne37` proves this proposition by Abel summation.
-/

open scoped Classical BigOperators Topology

namespace Fermat.Irregular.CyclotomicLValue37

noncomputable section

open Filter Finset
open Fermat.Irregular.CyclotomicPlaces37
open Fermat.Irregular.CyclotomicDirichlet37
open Fermat.Irregular.CyclotomicLogDet

private lemma exists_tendsto_boundary_series_aux
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ l : ℂ, Tendsto (fun n ↦ ∑ i ∈ range n, z ^ (i + 1) / (i + 1))
      atTop (𝓝 l) := by
  have hfanti : Antitone (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹) := by
    refine antitone_nat_of_succ_le (fun n ↦ ?_)
    gcongr
    omega
  have hfzero : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hzsub : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  have hbound (n : ℕ) :
      ‖∑ i ∈ range n, z ^ (i + 1)‖ ≤ 2 / ‖z - 1‖ := by
    have hsum : (∑ i ∈ range n, z ^ (i + 1)) =
        z * ∑ i ∈ range n, z ^ i := by
      rw [Finset.mul_sum]
      simp_rw [pow_succ']
    rw [hsum, norm_mul, hz, one_mul]
    calc
      ‖∑ i ∈ range n, z ^ i‖ =
          ‖(∑ i ∈ range n, z ^ i) * (z - 1)‖ / ‖z - 1‖ := by
            rw [norm_mul, mul_div_cancel_right₀ _ (ne_of_gt hzsub)]
      _ = ‖z ^ n - 1‖ / ‖z - 1‖ := by rw [geom_sum_mul]
      _ ≤ 2 / ‖z - 1‖ := by
        gcongr
        calc
          ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_pow, hz]; norm_num
  have hcauchy : CauchySeq (fun n ↦
      ∑ i ∈ range n, ((i + 1 : ℕ) : ℝ)⁻¹ • z ^ (i + 1)) :=
    hfanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hfzero hbound
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨l, ?_⟩
  have hfun :
      (fun n ↦ ∑ i ∈ range n, z ^ (i + 1) / (i + 1)) =
        (fun n ↦ ∑ i ∈ range n, ((i + 1 : ℕ) : ℝ)⁻¹ • z ^ (i + 1)) := by
    funext n
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    rw [Complex.real_smul]
    simp only [div_eq_mul_inv, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one, Complex.ofReal_inv]
    ring
  rw [hfun]
  exact hl

private lemma exists_tendsto_boundary_series
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ l : ℂ, Tendsto (fun n ↦ ∑ i ∈ range n, z ^ i / i) atTop (𝓝 l) := by
  obtain ⟨l, hl⟩ := exists_tendsto_boundary_series_aux hz hz1
  refine ⟨l, (Filter.tendsto_add_atTop_iff_nat 1).mp ?_⟩
  convert hl using 1
  funext n
  rw [Finset.sum_range_succ']
  simp

lemma one_sub_mem_slitPlane_of_norm_eq_one
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    1 - z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simp only [Complex.sub_re, Complex.one_re]
  have hle : z.re ≤ 1 := by simpa [hz] using Complex.re_le_norm z
  rw [sub_pos]
  exact lt_of_le_of_ne hle fun hre ↦ hz1 (by
    have him : z.im = 0 := Complex.abs_re_eq_norm.mp (by simp [hre, hz])
    apply Complex.ext <;> simp [hre, him])

/-- The naturally ordered boundary logarithm series on the unit circle. -/
theorem tendsto_boundary_series_neg_log
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (fun n ↦ ∑ i ∈ range n, z ^ i / i) atTop
      (𝓝 (-Complex.log (1 - z))) := by
  obtain ⟨l, hl⟩ := exists_tendsto_boundary_series hz hz1
  have hab := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  let F : ℂ → ℂ := fun w ↦ ∑' n : ℕ, (z ^ n / n) * w ^ n
  let G : ℂ → ℂ := fun w ↦ -Complex.log (1 - w * z)
  have heq : F =ᶠ[((𝓝[<] (1 : ℝ)).map Complex.ofReal)] G := by
    change ∀ᶠ w in (𝓝[<] (1 : ℝ)).map Complex.ofReal, F w = G w
    rw [Filter.eventually_map]
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono (show 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from inf_le_left)
        (Ioi_mem_nhds zero_lt_one)] with r hrlt hrpos
    have hrnorm : ‖(r : ℂ) * z‖ < 1 := by
      rw [norm_mul, Complex.norm_real, hz, mul_one]
      simpa [Real.norm_eq_abs, abs_of_pos hrpos] using hrlt
    dsimp only [F, G]
    calc
      (∑' n : ℕ, z ^ n / n * (r : ℂ) ^ n) =
          ∑' n : ℕ, ((r : ℂ) * z) ^ n / n := by
        apply tsum_congr
        intro n
        rw [mul_pow]
        ring
      _ = -Complex.log (1 - (r : ℂ) * z) :=
        (Complex.hasSum_taylorSeries_neg_log hrnorm).tsum_eq
  have hmap : Tendsto id ((𝓝[<] (1 : ℝ)).map Complex.ofReal) (𝓝 (1 : ℂ)) := by
    have hofreal : Tendsto Complex.ofReal (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
    exact hofreal
  have hGcont : ContinuousAt G (1 : ℂ) := by
    change ContinuousAt (fun w : ℂ ↦ -Complex.log (1 - w * z)) 1
    exact ((continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).clog
      (by simpa using one_sub_mem_slitPlane_of_norm_eq_one hz hz1)).neg
  have hG : Tendsto G ((𝓝[<] (1 : ℝ)).map Complex.ofReal)
      (𝓝 (-Complex.log (1 - z))) := by
    simpa [G] using hGcont.tendsto.comp hmap
  have hF : Tendsto F ((𝓝[<] (1 : ℝ)).map Complex.ofReal)
      (𝓝 (-Complex.log (1 - z))) := hG.congr' heq.symm
  have hab' : Tendsto F ((𝓝[<] (1 : ℝ)).map Complex.ofReal) (𝓝 l) := by
    simpa [F] using hab
  have hlvalue : l = -Complex.log (1 - z) := tendsto_nhds_unique hab' hF
  simpa [hlvalue] using hl

lemma stdAddChar37_eq_eta37_pow_val (a : ZMod 37) :
    ZMod.stdAddChar a = eta37 ^ a.val := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  change Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / 37) = _
  simp only [eta37]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma norm_stdAddChar37 (a : ZMod 37) : ‖ZMod.stdAddChar a‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

lemma stdAddChar37_ne_one {a : ZMod 37} (ha : a ≠ 0) :
    ZMod.stdAddChar a ≠ 1 := by
  intro h
  apply ha
  apply ZMod.injective_stdAddChar
  simpa using h

lemma stdAddChar37_neg (a : ZMod 37) :
    ZMod.stdAddChar (-a) = starRingEnd ℂ (ZMod.stdAddChar a) := by
  rw [AddChar.map_neg_eq_inv]
  exact Complex.inv_eq_conj (norm_stdAddChar37 a)

lemma one_sub_stdAddChar37_mem_slitPlane {a : ZMod 37} (ha : a ≠ 0) :
    1 - ZMod.stdAddChar a ∈ Complex.slitPlane :=
  one_sub_mem_slitPlane_of_norm_eq_one (norm_stdAddChar37 a)
    (stdAddChar37_ne_one ha)

lemma log_one_sub_stdAddChar37_neg {a : ZMod 37} (ha : a ≠ 0) :
    Complex.log (1 - ZMod.stdAddChar (-a)) =
      starRingEnd ℂ (Complex.log (1 - ZMod.stdAddChar a)) := by
  rw [stdAddChar37_neg]
  have hconj : 1 - starRingEnd ℂ (ZMod.stdAddChar a) =
      starRingEnd ℂ (1 - ZMod.stdAddChar a) := by simp
  rw [hconj, Complex.log_conj]
  exact Complex.slitPlane_arg_ne_pi (one_sub_stdAddChar37_mem_slitPlane ha)

lemma log_one_sub_stdAddChar37_pair {a : ZMod 37} (ha : a ≠ 0) :
    Complex.log (1 - ZMod.stdAddChar a) +
        Complex.log (1 - ZMod.stdAddChar (-a)) =
      (2 * Real.log ‖1 - ZMod.stdAddChar a‖ : ℝ) := by
  rw [log_one_sub_stdAddChar37_neg ha, Complex.add_conj, Complex.log_re]

lemma log_one_sub_stdAddChar37_pair_all (a : ZMod 37) :
    Complex.log (1 - ZMod.stdAddChar a) +
        Complex.log (1 - ZMod.stdAddChar (-a)) =
      (2 * Real.log ‖1 - ZMod.stdAddChar a‖ : ℝ) := by
  by_cases ha : a = 0
  · subst a
    simp
  · exact log_one_sub_stdAddChar37_pair ha

/-- The chord sum before pairing conjugate logarithms. -/
def complexDirichletChordLogSum37 (ψ : DirichletCharacter ℂ 37) : ℂ :=
  ∑ a : ZMod 37, Complex.log (1 - ZMod.stdAddChar a) * ψ⁻¹ a

/-- For an even character, pairing a root with its inverse turns the complex logarithms into
the real chord logarithms used by the regulator. -/
lemma complexDirichletChordLogSum37_eq_full_of_even
    {ψ : DirichletCharacter ℂ 37} (hψ : ψ.Even) :
    complexDirichletChordLogSum37 ψ = fullDirichletChordLogSum37 ψ := by
  have hcneg (a : ZMod 37) : ψ⁻¹ (-a) = ψ⁻¹ a := by
    rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', hψ.eval_neg]
  have hneg :
      (∑ a : ZMod 37, Complex.log (1 - ZMod.stdAddChar (-a)) * ψ⁻¹ a) =
        complexDirichletChordLogSum37 ψ := by
    rw [complexDirichletChordLogSum37]
    refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun a ↦ ?_)
    simp only [Equiv.neg_apply, hcneg]
  have hdouble : 2 * complexDirichletChordLogSum37 ψ =
      2 * ∑ a : ZMod 37,
        (Real.log ‖1 - ZMod.stdAddChar a‖ : ℂ) * ψ⁻¹ a := by
    calc
      2 * complexDirichletChordLogSum37 ψ =
          complexDirichletChordLogSum37 ψ + complexDirichletChordLogSum37 ψ := by ring
      _ = complexDirichletChordLogSum37 ψ +
          ∑ a : ZMod 37, Complex.log (1 - ZMod.stdAddChar (-a)) * ψ⁻¹ a := by
            rw [hneg]
      _ = ∑ a : ZMod 37,
          (Complex.log (1 - ZMod.stdAddChar a) * ψ⁻¹ a +
            Complex.log (1 - ZMod.stdAddChar (-a)) * ψ⁻¹ a) := by
            rw [complexDirichletChordLogSum37, Finset.sum_add_distrib]
      _ = ∑ a : ZMod 37,
          2 * ((Real.log ‖1 - ZMod.stdAddChar a‖ : ℂ) * ψ⁻¹ a) := by
            apply Fintype.sum_congr
            intro a
            rw [← add_mul, log_one_sub_stdAddChar37_pair_all]
            push_cast
            ring
      _ = 2 * ∑ a : ZMod 37,
          (Real.log ‖1 - ZMod.stdAddChar a‖ : ℂ) * ψ⁻¹ a := by
            rw [Finset.mul_sum]
  apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
  rw [hdouble]
  rw [fullDirichletChordLogSum37]
  apply congrArg (2 * ·)
  apply Fintype.sum_congr
  intro a
  rw [stdAddChar37_eq_eta37_pow_val]

/-- Natural-order partial sums of a Dirichlet series at s = 1. -/
def dirichletSeriesPartial37
    (ψ : DirichletCharacter ℂ 37) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, ψ n / n

/-- The same partial sum before the finite additive Fourier transform. -/
def additiveChordSeriesPartial37
    (ψ : DirichletCharacter ℂ 37) (N : ℕ) : ℂ :=
  ∑ a : ZMod 37,
    (∑ n ∈ range N, (ZMod.stdAddChar a) ^ n / n) * ψ⁻¹ a

/-- The boundary logarithm theorem, summed over the 37 additive roots. -/
lemma tendsto_additiveChordSeriesPartial37
    (ψ : DirichletCharacter ℂ 37) :
    Tendsto (additiveChordSeriesPartial37 ψ) atTop
      (𝓝 (-complexDirichletChordLogSum37 ψ)) := by
  have ha (a : ZMod 37) :
      Tendsto
        (fun N ↦ (∑ n ∈ range N, (ZMod.stdAddChar a) ^ n / n) * ψ⁻¹ a)
        atTop
        (𝓝 ((-Complex.log (1 - ZMod.stdAddChar a)) * ψ⁻¹ a)) := by
    by_cases ha0 : a = 0
    · subst a
      have hzero : ψ⁻¹ (0 : ZMod 37) = 0 := (ψ⁻¹).map_zero' (by norm_num)
      simp [hzero]
    · exact (tendsto_boundary_series_neg_log (norm_stdAddChar37 a)
        (stdAddChar37_ne_one ha0)).mul_const _
  have hsum := tendsto_finsetSum (s := Finset.univ) (fun a _ ↦ ha a)
  simpa only [additiveChordSeriesPartial37, complexDirichletChordLogSum37,
    Finset.sum_neg_distrib, neg_mul] using hsum

/-- The exact finite Fourier transform, with Mathlib's positive-exponential additive character
and the inverse-character Gauss sum. -/
lemma sum_stdAddChar37_pow_mul_inv_eq_gaussSum_mul
    {ψ : DirichletCharacter ℂ 37} (hψ : ψ.IsPrimitive) (n : ℕ) :
    (∑ a : ZMod 37, (ZMod.stdAddChar a) ^ n * ψ⁻¹ a) =
      gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37)) * ψ n := by
  have hψinv : ψ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def] at hψ ⊢
    rw [DirichletCharacter.conductor_inv]
    exact hψ
  have hfourier := hψinv.fourierTransform_eq_inv_mul_gaussSum (-(n : ZMod 37))
  calc
    (∑ a : ZMod 37, (ZMod.stdAddChar a) ^ n * ψ⁻¹ a) =
        ZMod.dft (fun a : ZMod 37 ↦ (ψ⁻¹ : DirichletCharacter ℂ 37) a)
          (-(n : ZMod 37)) := by
      rw [ZMod.dft_apply]
      apply Fintype.sum_congr
      intro a
      simp only [smul_eq_mul]
      congr 1
      rw [← AddChar.map_nsmul_eq_pow]
      congr 1
      simp only [nsmul_eq_mul, mul_neg, neg_neg]
      ring
    _ = ψ n * gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37)) := by
      simpa only [neg_neg, inv_inv] using hfourier
    _ = gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37)) * ψ n := by ring

lemma additiveChordSeriesPartial37_eq_gaussSum_mul
    {ψ : DirichletCharacter ℂ 37} (hψ : ψ.IsPrimitive) (N : ℕ) :
    additiveChordSeriesPartial37 ψ N =
      gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37)) *
        dirichletSeriesPartial37 ψ N := by
  rw [additiveChordSeriesPartial37, dirichletSeriesPartial37]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ x ∈ range N, ∑ a : ZMod 37,
        (ZMod.stdAddChar a) ^ x / x * ψ⁻¹ a) =
        ∑ x ∈ range N,
          (∑ a : ZMod 37, (ZMod.stdAddChar a) ^ x * ψ⁻¹ a) / x := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_div]
      apply Fintype.sum_congr
      intro a
      ring
    _ = ∑ x ∈ range N,
        (gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37)) * ψ x) / x := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [sum_stdAddChar37_pow_mul_inv_eq_gaussSum_mul hψ]
    _ = gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37)) *
        ∑ x ∈ range N, ψ x / x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

/-- Once the natural-order Dirichlet series is identified with LFunction at one, the exact
chord-log formula follows. -/
lemma fullDirichletChordLogSum37_eq_neg_gaussSum_mul_LFunction_of_tendsto
    {χ : RealResidueGroup37 →* ℂˣ} (hχ : χ ≠ 1)
    (hL : Tendsto
      (dirichletSeriesPartial37 (quotientCharacterToDirichlet37 χ)) atTop
      (𝓝 ((quotientCharacterToDirichlet37 χ).LFunction 1))) :
    fullDirichletChordLogSum37 (quotientCharacterToDirichlet37 χ) =
      -gaussSum (quotientCharacterToDirichlet37 χ)⁻¹
          (ZMod.stdAddChar (N := 37)) *
        (quotientCharacterToDirichlet37 χ).LFunction 1 := by
  let ψ := quotientCharacterToDirichlet37 χ
  have hprim : ψ.IsPrimitive := quotientCharacterToDirichlet37_isPrimitive hχ
  have haddLog := tendsto_additiveChordSeriesPartial37 ψ
  have hLψ : Tendsto (dirichletSeriesPartial37 ψ) atTop (𝓝 (ψ.LFunction 1)) := by
    simpa only [ψ] using hL
  have haddL : Tendsto (additiveChordSeriesPartial37 ψ) atTop
      (𝓝 (gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37)) * ψ.LFunction 1)) := by
    have hmul := ((tendsto_const_nhds (x :=
      gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37)))).mul hLψ)
    exact hmul.congr' (Eventually.of_forall fun N ↦
      (additiveChordSeriesPartial37_eq_gaussSum_mul hprim N).symm)
  have heq : -complexDirichletChordLogSum37 ψ =
      gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37)) * ψ.LFunction 1 :=
    tendsto_nhds_unique haddLog haddL
  calc
    fullDirichletChordLogSum37 (quotientCharacterToDirichlet37 χ) =
        complexDirichletChordLogSum37 ψ := by
      symm
      exact complexDirichletChordLogSum37_eq_full_of_even
        (quotientCharacterToDirichlet37_even χ)
    _ = -gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37)) * ψ.LFunction 1 := by
      calc
        complexDirichletChordLogSum37 ψ =
            -(-complexDirichletChordLogSum37 ψ) := by ring
        _ = -(gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37)) * ψ.LFunction 1) :=
          congrArg Neg.neg heq
        _ = -gaussSum ψ⁻¹ (ZMod.stdAddChar (N := 37)) * ψ.LFunction 1 := by ring

/-- The analytic-continuation input isolated by this module for the chord-log formula: the natural-order
Dirichlet series of every nontrivial even character modulo 37 converges at the boundary to
Mathlib's analytically continued LFunction value. -/
def DirichletSeriesAtOneFormula37 : Prop :=
  ∀ (χ : RealResidueGroup37 →* ℂˣ), χ ≠ 1 →
    Tendsto (dirichletSeriesPartial37 (quotientCharacterToDirichlet37 χ)) atTop
      (𝓝 ((quotientCharacterToDirichlet37 χ).LFunction 1))

theorem chordLogLValueFormula37_of_dirichletSeriesAtOne
    (hseries : DirichletSeriesAtOneFormula37) :
    ChordLogLValueFormula37 := by
  intro χ hχ
  exact fullDirichletChordLogSum37_eq_neg_gaussSum_mul_LFunction_of_tendsto
    hχ (hseries χ hχ)

end
end Fermat.Irregular.CyclotomicLValue37
