import Fermat.Irregular.CyclotomicLValue37

/-!
# Natural convergence of the exponent-37 Dirichlet series at one

This file closes the analytic-continuation seam left by `CyclotomicLValue37`.  Periodicity bounds
the character partial sums, so Dirichlet's test gives a natural-order limit at `s = 1`.  Abel
summation identifies the absolutely convergent series at `1 + t` with a positive telescoping
average of those partial sums.  A Toeplitz-limit argument sends that average to the natural-order
limit as `t → 0⁺`, while continuity of Mathlib's nontrivial Dirichlet `LFunction` sends the same
series to `LFunction 1`.

Thus `DirichletSeriesAtOneFormula37` and consequently `ChordLogLValueFormula37` are theorems,
without an analytic hypothesis.
-/

open scoped Classical BigOperators Topology
open Filter Finset

namespace Fermat.Irregular.CyclotomicSeriesAtOne37

noncomputable section

open Fermat.Irregular.CyclotomicLValue37
open Fermat.Irregular.CyclotomicDirichlet37
open Fermat.Irregular.CyclotomicLogDet
open Fermat.Irregular.CyclotomicPlaces37

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fintype (RealResidueGroup37 →* ℂˣ) := Fintype.ofFinite _

def characterPartial37 (ψ : DirichletCharacter ℂ 37) (n : ℕ) : ℂ :=
  ∑ i ∈ range n, ψ i

lemma sum_character_block37 {ψ : DirichletCharacter ℂ 37} (hψ : ψ ≠ 1) (n : ℕ) :
    ∑ i ∈ range 37, ψ ((n + i : ℕ) : ZMod 37) = 0 := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin 37, ψ (((n + i.val : ℕ) : ZMod 37))) =
        ∑ a : ZMod 37, ψ ((n : ZMod 37) + a) := by
      refine Fintype.sum_equiv (ZMod.finEquiv 37) _ _ (fun i ↦ ?_)
      congr 1
      rw [Nat.cast_add]
      congr 1
      change ((i.val : ℕ) : ZMod 37) = i
      apply Fin.ext
      exact Nat.mod_eq_of_lt i.isLt
    _ = ∑ a : ZMod 37, ψ a := by
      simpa [add_comm] using
        Equiv.sum_comp (Equiv.addRight (n : ZMod 37)) (fun a : ZMod 37 ↦ ψ a)
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hψ

lemma characterPartial37_add_period {ψ : DirichletCharacter ℂ 37} (hψ : ψ ≠ 1) (n : ℕ) :
    characterPartial37 ψ (n + 37) = characterPartial37 ψ n := by
  rw [characterPartial37, Finset.sum_range_add]
  change (∑ x ∈ range n, ψ x) +
    ∑ x ∈ range 37, ψ (((n + x : ℕ) : ZMod 37)) = _
  rw [sum_character_block37 hψ, add_zero]
  rfl

def characterPartialBound37 (ψ : DirichletCharacter ℂ 37) : ℝ :=
  ∑ i ∈ range 37, ‖ψ i‖

lemma norm_characterPartial37_le {ψ : DirichletCharacter ℂ 37} (hψ : ψ ≠ 1) (n : ℕ) :
    ‖characterPartial37 ψ n‖ ≤ characterPartialBound37 ψ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 37
      · rw [characterPartial37, characterPartialBound37]
        calc
          ‖∑ i ∈ range n, ψ i‖ ≤ ∑ i ∈ range n, ‖ψ i‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ range 37, ‖ψ i‖ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact range_mono hn.le
            · intro i hi hnot
              exact norm_nonneg _
      · have h37 : 37 ≤ n := Nat.le_of_not_gt hn
        have hsub : n - 37 < n := Nat.sub_lt (by omega) (by omega)
        calc
          ‖characterPartial37 ψ n‖ =
              ‖characterPartial37 ψ ((n - 37) + 37)‖ := by
                congr 2
                all_goals omega
          _ = ‖characterPartial37 ψ (n - 37)‖ := by
            rw [characterPartial37_add_period hψ]
          _ ≤ characterPartialBound37 ψ := ih (n - 37) hsub

lemma dirichletSeriesPartial37_succ (ψ : DirichletCharacter ℂ 37) (n : ℕ) :
    dirichletSeriesPartial37 ψ (n + 1) =
      ∑ i ∈ range n, ψ (i + 1) / (i + 1) := by
  rw [dirichletSeriesPartial37, Finset.sum_range_succ']
  simp [ψ.map_zero' (by norm_num)]

lemma exists_tendsto_dirichletSeriesPartial37
    {ψ : DirichletCharacter ℂ 37} (hψ : ψ ≠ 1) :
    ∃ l : ℂ, Tendsto (dirichletSeriesPartial37 ψ) atTop (𝓝 l) := by
  have hfanti : Antitone (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹) := by
    refine antitone_nat_of_succ_le (fun n ↦ ?_)
    gcongr
    omega
  have hfzero : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hbound (n : ℕ) :
      ‖∑ i ∈ range n, ψ ((i + 1 : ℕ) : ZMod 37)‖ ≤
        characterPartialBound37 ψ := by
    have heq : (∑ i ∈ range n, ψ ((i + 1 : ℕ) : ZMod 37)) =
        characterPartial37 ψ (n + 1) := by
      rw [characterPartial37, Finset.sum_range_succ']
      simp [ψ.map_zero' (by norm_num)]
    rw [heq]
    exact norm_characterPartial37_le hψ _
  have hcauchyShift : CauchySeq (fun n ↦
      ∑ i ∈ range n, ((i + 1 : ℕ) : ℝ)⁻¹ •
        ψ ((i + 1 : ℕ) : ZMod 37)) :=
    hfanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hfzero hbound
  have hfun :
      (fun n ↦ dirichletSeriesPartial37 ψ (n + 1)) =
        (fun n ↦ ∑ i ∈ range n, ((i + 1 : ℕ) : ℝ)⁻¹ •
          ψ ((i + 1 : ℕ) : ZMod 37)) := by
    funext n
    rw [dirichletSeriesPartial37_succ]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    rw [Complex.real_smul]
    simp only [div_eq_mul_inv, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one, Complex.ofReal_inv]
    ring
  rw [← hfun] at hcauchyShift
  have hcauchy : CauchySeq (dirichletSeriesPartial37 ψ) :=
    (cauchySeq_shift 1).mp hcauchyShift
  exact cauchySeq_tendsto_of_complete hcauchy

def dirichletAbelWeight (t : ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ) ^ (-t)

def dirichletAbelDifference (t : ℝ) (n : ℕ) : ℝ :=
  dirichletAbelWeight t n - dirichletAbelWeight t (n + 1)

lemma dirichletAbelWeight_antitone {t : ℝ} (ht : 0 ≤ t) :
    Antitone (dirichletAbelWeight t) := by
  intro m n hmn
  rw [dirichletAbelWeight, dirichletAbelWeight]
  apply Real.rpow_le_rpow_of_nonpos (by positivity)
  · exact_mod_cast Nat.add_le_add_right hmn 1
  · linarith

lemma dirichletAbelDifference_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ dirichletAbelDifference t n :=
  sub_nonneg.mpr (dirichletAbelWeight_antitone ht (Nat.le_succ n))

lemma tendsto_dirichletAbelWeight_atTop {t : ℝ} (ht : 0 < t) :
    Tendsto (dirichletAbelWeight t) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
    exact (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).atTop_add tendsto_const_nhds
  exact (tendsto_rpow_neg_atTop ht).comp hbase

lemma hasSum_dirichletAbelDifference {t : ℝ} (ht : 0 < t) :
    HasSum (dirichletAbelDifference t) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (dirichletAbelDifference_nonneg ht.le) 1]
  have hw := tendsto_dirichletAbelWeight_atTop ht
  have hpartial :
      (fun n ↦ ∑ i ∈ range n, dirichletAbelDifference t i) =
        (fun n ↦ 1 - dirichletAbelWeight t n) := by
    funext n
    simp_rw [dirichletAbelDifference]
    rw [Finset.sum_range_sub']
    simp [dirichletAbelWeight]
  rw [hpartial]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hw

lemma tendsto_dirichletAbelDifference_zero (n : ℕ) :
    Tendsto (fun t : ℝ ↦ dirichletAbelDifference t n) (𝓝 0) (𝓝 0) := by
  have h₁ : Tendsto (fun t : ℝ ↦ dirichletAbelWeight t n) (𝓝 0) (𝓝 1) := by
    have hc : ContinuousAt (fun t : ℝ ↦ (n + 1 : ℝ) ^ (-t)) 0 :=
      (Real.continuous_const_rpow (by positivity : (n + 1 : ℝ) ≠ 0)).continuousAt.comp
        continuousAt_neg
    simpa [dirichletAbelWeight] using hc.tendsto
  have h₂ : Tendsto (fun t : ℝ ↦ dirichletAbelWeight t (n + 1)) (𝓝 0) (𝓝 1) := by
    have hc : ContinuousAt (fun t : ℝ ↦ (n + 1 + 1 : ℝ) ^ (-t)) 0 :=
      (Real.continuous_const_rpow (by positivity : (n + 1 + 1 : ℝ) ≠ 0)).continuousAt.comp
        continuousAt_neg
    simpa [dirichletAbelWeight] using hc.tendsto
  simpa [dirichletAbelDifference] using h₁.sub h₂

lemma summable_sub_mul_dirichletAbelDifference
    {A : ℕ → ℂ} {l : ℂ} (hA : Tendsto A atTop (𝓝 l))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun n ↦ (A n - l) * (dirichletAbelDifference t n : ℂ)) := by
  have hbound : ∀ᶠ n in atTop, ‖A n - l‖ ≤ 1 := by
    filter_upwards [(Metric.tendsto_nhds.1 hA 1 zero_lt_one)] with n hn
    simpa [dist_eq_norm] using hn.le
  have hd : Summable (dirichletAbelDifference t) :=
    (hasSum_dirichletAbelDifference ht).summable
  apply Summable.of_norm_bounded_eventually hd
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hbound] with n hn
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (dirichletAbelDifference_nonneg ht.le n)]
  simpa using mul_le_of_le_one_left (dirichletAbelDifference_nonneg ht.le n) hn

lemma tendsto_tsum_mul_dirichletAbelDifference
    {A : ℕ → ℂ} {l : ℂ} (hA : Tendsto A atTop (𝓝 l)) :
    Tendsto
      (fun t : ℝ ↦ ∑' n, A n * (dirichletAbelDifference t n : ℂ))
      (𝓝[>] 0) (𝓝 l) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hAε := Metric.tendsto_nhds.1 hA (ε / 2) (half_pos hε)
  rcases (eventually_atTop.1 hAε) with ⟨N, hN⟩
  have hprefix : Tendsto
      (fun t : ℝ ↦ ∑ n ∈ range N,
        (A n - l) * (dirichletAbelDifference t n : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
    have hterm : ∀ n ∈ range N, Tendsto
        (fun t : ℝ ↦ (A n - l) * (dirichletAbelDifference t n : ℂ))
        (𝓝[>] 0) (𝓝 0) := by
      intro n hn
      have hdR : Tendsto (fun t : ℝ ↦ dirichletAbelDifference t n)
          (𝓝[>] 0) (𝓝 0) :=
        (tendsto_dirichletAbelDifference_zero n).mono_left inf_le_left
      have hdC : Tendsto (fun t : ℝ ↦ (dirichletAbelDifference t n : ℂ))
          (𝓝[>] 0) (𝓝 0) := by
        change Tendsto
          (Complex.ofRealCLM ∘ fun t : ℝ ↦ dirichletAbelDifference t n)
          (𝓝[>] 0) (𝓝 0)
        exact Complex.ofRealCLM.continuous.continuousAt.tendsto.comp hdR
      simpa using tendsto_const_nhds.mul hdC
    simpa using tendsto_finsetSum (range N) hterm
  have hprefixε : ∀ᶠ t in 𝓝[>] 0,
      ‖∑ n ∈ range N,
        (A n - l) * (dirichletAbelDifference t n : ℂ)‖ < ε / 2 := by
    filter_upwards [(Metric.tendsto_nhds.1 hprefix (ε / 2) (half_pos hε))] with t ht
    simpa [dist_eq_norm] using ht
  filter_upwards [self_mem_nhdsWithin, hprefixε] with t ht hprefix_t
  have htpos : 0 < t := ht
  let E : ℕ → ℂ := fun n ↦
    (A n - l) * (dirichletAbelDifference t n : ℂ)
  have hE : Summable E := by
    exact summable_sub_mul_dirichletAbelDifference hA htpos
  have hd : Summable (dirichletAbelDifference t) :=
    (hasSum_dirichletAbelDifference htpos).summable
  have hdC : HasSum
      (fun n ↦ (dirichletAbelDifference t n : ℂ)) 1 := by
    change HasSum
      (Complex.ofRealCLM ∘ dirichletAbelDifference t) (Complex.ofRealCLM 1)
    exact Complex.ofRealCLM.hasSum (hasSum_dirichletAbelDifference htpos)
  have hl : HasSum
      (fun n ↦ l * (dirichletAbelDifference t n : ℂ)) l := by
    simpa using hdC.mul_left l
  have hmain : Summable
      (fun n ↦ A n * (dirichletAbelDifference t n : ℂ)) := by
    simpa [E, sub_mul] using hE.add hl.summable
  have herror :
      (∑' n, A n * (dirichletAbelDifference t n : ℂ)) - l = ∑' n, E n := by
    rw [← hl.tsum_eq, ← hmain.tsum_sub hl.summable]
    congr 1
    funext n
    simp [E, sub_mul]
  have hdshift : Summable
      (fun n ↦ dirichletAbelDifference t (n + N)) :=
    (summable_nat_add_iff N).2 hd
  have hmass :
      (∑' n, dirichletAbelDifference t (n + N)) ≤ 1 := by
    have hsplit := hd.sum_add_tsum_nat_add N
    calc
      (∑' n, dirichletAbelDifference t (n + N)) ≤
          (∑ n ∈ range N, dirichletAbelDifference t n) +
            ∑' n, dirichletAbelDifference t (n + N) := by
        exact le_add_of_nonneg_left
          (sum_nonneg fun n hn ↦ dirichletAbelDifference_nonneg htpos.le n)
      _ = ∑' n, dirichletAbelDifference t n := hsplit
      _ = 1 := (hasSum_dirichletAbelDifference htpos).tsum_eq
  have htailTerm (n : ℕ) :
      ‖E (n + N)‖ ≤
        (ε / 2) * dirichletAbelDifference t (n + N) := by
    have hAN : ‖A (n + N) - l‖ ≤ ε / 2 := by
      have := hN (n + N) (by omega)
      simpa [dist_eq_norm] using this.le
    change ‖(A (n + N) - l) * (dirichletAbelDifference t (n + N) : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (dirichletAbelDifference_nonneg htpos.le (n + N))]
    exact mul_le_mul_of_nonneg_right hAN
      (dirichletAbelDifference_nonneg htpos.le (n + N))
  have hscaled : Summable
      (fun n ↦ (ε / 2) * dirichletAbelDifference t (n + N)) :=
    hdshift.mul_left (ε / 2)
  have htailNorm : Summable (fun n ↦ ‖E (n + N)‖) :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) htailTerm hscaled
  have htail : ‖∑' n, E (n + N)‖ ≤ ε / 2 := by
    calc
      ‖∑' n, E (n + N)‖ ≤ ∑' n, ‖E (n + N)‖ :=
        norm_tsum_le_tsum_norm htailNorm
      _ ≤ ∑' n, (ε / 2) * dirichletAbelDifference t (n + N) :=
        htailNorm.tsum_le_tsum htailTerm hscaled
      _ = (ε / 2) * ∑' n, dirichletAbelDifference t (n + N) :=
        tsum_mul_left
      _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hmass (half_pos hε).le
      _ = ε / 2 := mul_one _
  have hsplit := hE.sum_add_tsum_nat_add N
  calc
    dist (∑' n, A n * (dirichletAbelDifference t n : ℂ)) l = ‖∑' n, E n‖ := by
      rw [dist_eq_norm, herror]
    _ = ‖(∑ n ∈ range N, E n) + ∑' n, E (n + N)‖ := by rw [hsplit]
    _ ≤ ‖∑ n ∈ range N, E n‖ + ‖∑' n, E (n + N)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le (by simpa [E] using hprefix_t) htail
    _ = ε := by ring

def dirichletSeriesShiftedTerm37 (ψ : DirichletCharacter ℂ 37) (n : ℕ) : ℂ :=
  ψ (n + 1) / (n + 1)

def dirichletSeriesShiftedPartial37 (ψ : DirichletCharacter ℂ 37) (n : ℕ) : ℂ :=
  ∑ i ∈ range (n + 1), dirichletSeriesShiftedTerm37 ψ i

lemma dirichletSeriesShiftedPartial37_eq
    (ψ : DirichletCharacter ℂ 37) (n : ℕ) :
    dirichletSeriesShiftedPartial37 ψ n = dirichletSeriesPartial37 ψ (n + 2) := by
  rw [show n + 2 = (n + 1) + 1 by omega, dirichletSeriesPartial37_succ]
  rfl

lemma dirichletAbelWeightedTerm_eq_LSeriesTerm
    (ψ : DirichletCharacter ℂ 37) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (dirichletAbelWeight t n : ℂ) * dirichletSeriesShiftedTerm37 ψ n =
      LSeries.term (ψ ·) ((1 + t : ℝ) : ℂ) (n + 1) := by
  have hs : ((1 + t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < 1 + t by linarith))
  have hn : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  have hweight : (((n + 1 : ℝ) ^ (-t) : ℝ) : ℂ) =
      (((n : ℂ) + 1) ^ (t : ℂ))⁻¹ := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ))]
    push_cast
    rw [Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ))]
    norm_num [Nat.cast_add, Nat.cast_one]
  rw [LSeries.term_of_ne_zero' hs]
  rw [dirichletAbelWeight, dirichletSeriesShiftedTerm37]
  rw [hweight]
  push_cast
  rw [Complex.cpow_add _ _ hn, Complex.cpow_one]
  field_simp

lemma tsum_dirichletAbelWeighted_eq_LFunction
    (ψ : DirichletCharacter ℂ 37) {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, (dirichletAbelWeight t n : ℂ) *
      dirichletSeriesShiftedTerm37 ψ n) =
      ψ.LFunction ((1 + t : ℝ) : ℂ) := by
  have hre : 1 < (((1 + t : ℝ) : ℂ)).re := by simp; linarith
  have hsummable : Summable (LSeries.term (ψ ·) ((1 + t : ℝ) : ℂ)) :=
    ZMod.LSeriesSummable_of_one_lt_re ψ hre
  calc
    (∑' n : ℕ, (dirichletAbelWeight t n : ℂ) *
        dirichletSeriesShiftedTerm37 ψ n) =
        ∑' n : ℕ, LSeries.term (ψ ·) ((1 + t : ℝ) : ℂ) (n + 1) := by
      apply tsum_congr
      exact dirichletAbelWeightedTerm_eq_LSeriesTerm ψ ht
    _ = LSeries (ψ ·) ((1 + t : ℝ) : ℂ) := by
      rw [LSeries]
      simpa using hsummable.sum_add_tsum_nat_add 1
    _ = ψ.LFunction ((1 + t : ℝ) : ℂ) :=
      (DirichletCharacter.LFunction_eq_LSeries ψ hre).symm

def dirichletAbelKernel (t : ℝ) (A : ℕ → ℂ) (n : ℕ) : ℂ :=
  (dirichletAbelDifference t n : ℂ) * A n

lemma summable_dirichletAbelKernel {t : ℝ} (ht : 0 < t)
    {A : ℕ → ℂ} {l : ℂ} (hA : Tendsto A atTop (𝓝 l)) :
    Summable (dirichletAbelKernel t A) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto A hA)
  have hdSummable : Summable (dirichletAbelDifference t) :=
    (hasSum_dirichletAbelDifference ht).summable
  apply Summable.of_norm_bounded (hdSummable.mul_left C)
  intro n
  rw [dirichletAbelKernel, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (dirichletAbelDifference_nonneg ht.le n)]
  rw [mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC (A n) ⟨n, rfl⟩)
    (dirichletAbelDifference_nonneg ht.le n)

lemma tsum_dirichletAbelWeighted_eq_kernel
    (ψ : DirichletCharacter ℂ 37) {t : ℝ} (ht : 0 < t) {l : ℂ}
    (hA : Tendsto (dirichletSeriesShiftedPartial37 ψ) atTop (𝓝 l)) :
    (∑' n : ℕ, (dirichletAbelWeight t n : ℂ) *
      dirichletSeriesShiftedTerm37 ψ n) =
      ∑' n : ℕ, dirichletAbelKernel t (dirichletSeriesShiftedPartial37 ψ) n := by
  let b := dirichletSeriesShiftedTerm37 ψ
  let A := dirichletSeriesShiftedPartial37 ψ
  have hApartial (n : ℕ) : A n = ∑ i ∈ range (n + 1), b i := by rfl
  have hB : Tendsto (fun n ↦ ∑ i ∈ range n, b i) atTop (𝓝 l) := by
    apply (Filter.tendsto_add_atTop_iff_nat 1).mp
    change Tendsto A atTop (𝓝 l)
    exact hA
  have hboundary : Tendsto (fun n ↦
      dirichletAbelWeight t (n - 1) • (∑ i ∈ range n, b i)) atTop (𝓝 0) := by
    have hw : Tendsto (fun n ↦ dirichletAbelWeight t (n - 1)) atTop (𝓝 0) :=
      (tendsto_dirichletAbelWeight_atTop ht).comp (tendsto_sub_atTop_nat 1)
    simpa using hw.smul hB
  have hkernelSummable : Summable (dirichletAbelKernel t A) :=
    summable_dirichletAbelKernel ht hA
  have hkernelPartial : Tendsto (fun n ↦
      ∑ i ∈ range (n - 1), dirichletAbelKernel t A i) atTop
      (𝓝 (∑' i : ℕ, dirichletAbelKernel t A i)) :=
    hkernelSummable.hasSum.tendsto_sum_nat.comp (tendsto_sub_atTop_nat 1)
  have hparts (n : ℕ) :
      (∑ i ∈ range n, (dirichletAbelWeight t i : ℂ) * b i) =
        dirichletAbelWeight t (n - 1) • (∑ i ∈ range n, b i) +
          ∑ i ∈ range (n - 1), dirichletAbelKernel t A i := by
    rw [show (∑ i ∈ range n, (dirichletAbelWeight t i : ℂ) * b i) =
      ∑ i ∈ range n, dirichletAbelWeight t i • b i by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Complex.real_smul]]
    rw [Finset.sum_range_by_parts]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [dirichletAbelKernel, hApartial, Complex.real_smul]
    rw [dirichletAbelDifference]
    push_cast
    ring
  have hweightedSummable : Summable (fun n : ℕ ↦
      (dirichletAbelWeight t n : ℂ) * b n) := by
    have hre : 1 < (((1 + t : ℝ) : ℂ)).re := by simp; linarith
    have hs := ZMod.LSeriesSummable_of_one_lt_re ψ hre
    have hshift : Summable (fun n : ℕ ↦
        LSeries.term (ψ ·) ((1 + t : ℝ) : ℂ) (n + 1)) :=
      (summable_nat_add_iff 1).mpr hs
    apply hshift.congr
    intro n
    exact (dirichletAbelWeightedTerm_eq_LSeriesTerm ψ ht n).symm
  apply tendsto_nhds_unique hweightedSummable.hasSum.tendsto_sum_nat
  have hlim := (hboundary.add hkernelPartial).congr'
    (Eventually.of_forall fun n ↦ (hparts n).symm)
  simpa only [zero_add, A] using hlim

lemma tendsto_dirichletSeriesPartial37_LFunction
    {ψ : DirichletCharacter ℂ 37} (hψ : ψ ≠ 1) :
    Tendsto (dirichletSeriesPartial37 ψ) atTop (𝓝 (ψ.LFunction 1)) := by
  obtain ⟨l, hl⟩ := exists_tendsto_dirichletSeriesPartial37 hψ
  have hA : Tendsto (dirichletSeriesShiftedPartial37 ψ) atTop (𝓝 l) := by
    have hshift := hl.comp (tendsto_add_atTop_nat 2)
    exact hshift.congr' (Eventually.of_forall fun n ↦
      (dirichletSeriesShiftedPartial37_eq ψ n).symm)
  have hkernel : Tendsto (fun t : ℝ ↦
      ∑' n : ℕ, dirichletAbelKernel t (dirichletSeriesShiftedPartial37 ψ) n)
      (𝓝[>] 0) (𝓝 l) := by
    simpa only [dirichletAbelKernel, mul_comm] using
      tendsto_tsum_mul_dirichletAbelDifference hA
  have hweighted : Tendsto (fun t : ℝ ↦
      ∑' n : ℕ, (dirichletAbelWeight t n : ℂ) *
        dirichletSeriesShiftedTerm37 ψ n) (𝓝[>] 0) (𝓝 l) := by
    apply hkernel.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (tsum_dirichletAbelWeighted_eq_kernel ψ ht hA).symm
  have hLright : Tendsto (fun t : ℝ ↦ ψ.LFunction ((1 + t : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (ψ.LFunction 1)) := by
    have hparam : Tendsto (fun t : ℝ ↦ ((1 + t : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
      have hc : ContinuousAt (fun t : ℝ ↦ ((1 + t : ℝ) : ℂ)) 0 := by fun_prop
      simpa only [add_zero, Complex.ofReal_one] using hc.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    exact (DirichletCharacter.differentiable_LFunction hψ).continuous.continuousAt.tendsto.comp
      hparam
  have hLweighted : Tendsto (fun t : ℝ ↦
      ∑' n : ℕ, (dirichletAbelWeight t n : ℂ) *
        dirichletSeriesShiftedTerm37 ψ n)
      (𝓝[>] 0) (𝓝 (ψ.LFunction 1)) := by
    apply hLright.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (tsum_dirichletAbelWeighted_eq_LFunction ψ ht).symm
  have hlvalue : l = ψ.LFunction 1 := tendsto_nhds_unique hweighted hLweighted
  simpa only [hlvalue] using hl

theorem dirichletSeriesAtOneFormula37 : DirichletSeriesAtOneFormula37 := by
  intro χ hχ
  apply tendsto_dirichletSeriesPartial37_LFunction
  intro htriv
  apply hχ
  exact (quotientCharacterToDirichlet37_eq_one_iff χ).mp htriv

/-- The exponent-37 chord-log identity, now with its boundary convergence discharged. -/
theorem chordLogLValueFormula37 : ChordLogLValueFormula37 :=
  chordLogLValueFormula37_of_dirichletSeriesAtOne dirichletSeriesAtOneFormula37

/-- The archimedean determinant endpoint with no remaining per-character analytic hypothesis. -/
theorem abs_explicitSineDet_eq_sqrt_pow_mul_norm_prod_LFunction_unconditional :
    |explicitSineMatrix37.det| = (Real.sqrt 37) ^ 17 *
      ‖∏ χ : { χ : RealResidueGroup37 →* ℂˣ // χ ≠ 1 },
        (quotientCharacterToDirichlet37 χ).LFunction 1‖ :=
  abs_explicitSineDet_eq_sqrt_pow_mul_norm_prod_LFunction chordLogLValueFormula37

end
end Fermat.Irregular.CyclotomicSeriesAtOne37
