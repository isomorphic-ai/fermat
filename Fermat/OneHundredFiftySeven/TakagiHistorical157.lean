import Fermat.Irregular.TakagiReflection157
import Fermat.OneHundredFiftySeven.VandiverHistorical

set_option maxRecDepth 50000

/-!
# Unconditional Takagi--Furtwängler step in Vandiver's historical proof

The universal predicate `LemmaOne K 157` is stronger than the instance
used by Vandiver's equation (7a).  The historical radicand is the explicit
conjugate pair

`q₊ * conj(q₊)^156`.

The conjugation-fixed Kummer extension constructed in
`TakagiReflection157` therefore proves the required historical equation
directly, without taking the universal class-field-theoretic predicate as
an input.
-/

open scoped NumberField

namespace Fermat.OneHundredFiftySeven.TakagiHistorical157

noncomputable section

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverLemmaOne
open Fermat.Irregular.TakagiReflection157
open Fermat.OneHundredFiftySeven.VandiverHistorical

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {157} ℚ K]

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 157) K (by norm_num)

set_option maxRecDepth 50000 in
/-- Vandiver's historical equation (7a), now discharged by the explicit
conjugation-fixed unramified Kummer extension and Hilbert 94. -/
theorem exists_historicalEquationSevenA157_unconditional
    {ζ : K} (hζ : IsPrimitiveRoot ζ 157) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ∃ r : 𝓞 K,
      historicalZetaFactorIdeal157 hζ s *
          historicalInverseZetaFactorIdeal157 hζ s ^ 156 =
        Ideal.span {r} := by
  exact exists_conjugatePairEquationSevenAGenerator157 hζ
    (historicalZetaFactorIdeal157 hζ s)
    (historicalInverseZetaFactorIdeal157 hζ s)
    (historicalZetaFactor157 hζ s)
    (normalizedHistoricalInverseZetaFactor157 hζ s)
    (historicalZetaFactorIdeal_pow157 hζ s)
    (historicalInverseZetaFactorIdeal_pow157 hζ s)
    (ringOfIntegersComplexConj_historicalZetaFactor157 hζ s hs)
    (historicalConjugateFactorProduct_isKummerPrimary157 hζ s hs)

set_option maxRecDepth 50000 in
/-- Vandiver's historical equation (8), with the former Lemma-1 premise
removed.  Equation (7a) is supplied above; equation (7d), nonvanishing,
and the Bézout ideal calculation are the existing kernel-checked
historical results. -/
theorem exists_historicalEquationEight157_unconditional
    {ζ : K} (hζ : IsPrimitiveRoot ζ 157) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ),
      historicalZetaFactorIdeal157 hζ s = Ideal.span {ρ} ∧
      historicalZetaFactor157 hζ s = η * ρ ^ 157 := by
  obtain ⟨r, hsevenA⟩ :=
    exists_historicalEquationSevenA157_unconditional hζ s hs
  obtain ⟨t, hsevenD⟩ :=
    exists_historicalEquationSevenD157 hζ s hs
  obtain ⟨hI0, hJ0⟩ :=
    historicalFactorIdeals_ne_zero157 hζ s hs
  exact exists_equationEight_of_sevenASevenD157
    (historicalZetaFactorIdeal157 hζ s)
    (historicalInverseZetaFactorIdeal157 hζ s)
    (historicalZetaFactor157 hζ s)
    (normalizedHistoricalInverseZetaFactor157 hζ s)
    r t hI0 hJ0
    (historicalZetaFactorIdeal_pow157 hζ s)
    (historicalInverseZetaFactorIdeal_pow157 hζ s)
    hsevenA hsevenD

set_option maxRecDepth 50000 in
/-- Unconditional equation (8) with its coefficient unit fixed by complex
conjugation. -/
theorem exists_historicalEquationEight_realUnit157_unconditional
    {ζ : K} (hζ : IsPrimitiveRoot ζ 157) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ),
      historicalZetaFactorIdeal157 hζ s = Ideal.span {ρ} ∧
      historicalZetaFactor157 hζ s = η * ρ ^ 157 ∧
      NumberField.IsCMField.unitsComplexConj K η = η := by
  obtain ⟨ρ, η, hI, heq⟩ :=
    exists_historicalEquationEight157_unconditional hζ s hs
  exact ⟨ρ, η, hI, heq,
    historicalEquationEight_unit_real157 hζ s hs ρ η heq⟩

set_option maxRecDepth 50000 in
/-- Unconditional paired equation (8) at `a = 1,-1`.  This is the literal
historical pair, now with the Takagi/Furtwängler premise discharged by the
explicit reflected extension. -/
theorem exists_historicalEquationEight_pair_one157_unconditional
    {ζ : K} (hζ : IsPrimitiveRoot ζ 157) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ∃ (ρone ρminus : 𝓞 K) (η : (𝓞 K)ˣ),
      NumberField.IsCMField.unitsComplexConj K η = η ∧
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
        (1 - (hζ.unit' : 𝓞 K)) * η * ρone ^ 157 ∧
      s.omega + (hζ.unit'⁻¹ : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit'⁻¹ : (𝓞 K)ˣ)) * η * ρminus ^ 157 ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K ρone = ρminus ∧
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ ρone ∧
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ ρminus := by
  obtain ⟨ρ, η₀, -, heq, hη₀real⟩ :=
    exists_historicalEquationEight_realUnit157_unconditional hζ s hs
  let η : (𝓞 K)ˣ := -η₀
  let ρminus : 𝓞 K :=
    NumberField.IsCMField.ringOfIntegersComplexConj K ρ
  have hηreal : NumberField.IsCMField.unitsComplexConj K η = η := by
    apply Units.ext
    change NumberField.IsCMField.ringOfIntegersComplexConj K
      (-(η₀ : 𝓞 K)) = -(η₀ : 𝓞 K)
    rw [map_neg]
    exact congrArg Neg.neg
      (congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hη₀real)
  have hqmul : historicalZetaFactor157 hζ s *
      ((hζ.unit' : 𝓞 K) - 1) =
        s.omega + s.theta * (hζ.unit' : 𝓞 K) :=
    div_zeta_sub_one_mul_zeta_sub_one
      (by norm_num : 157 ≠ 2) hζ
      (historicalState_regularEquation157 hζ s)
      (zetaNthRoot (K := K) (p := 157) hζ)
  have hone :
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
        (1 - (hζ.unit' : 𝓞 K)) * η * ρ ^ 157 := by
    calc
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
          s.omega + s.theta * (hζ.unit' : 𝓞 K) := by ring
      _ = historicalZetaFactor157 hζ s *
          ((hζ.unit' : 𝓞 K) - 1) := hqmul.symm
      _ = ((η₀ : 𝓞 K) * ρ ^ 157) *
          ((hζ.unit' : 𝓞 K) - 1) := by rw [heq]
      _ = (1 - (hζ.unit' : 𝓞 K)) * η * ρ ^ 157 := by
        dsimp [η]
        ring
  have hconjζ :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (hζ.unit' : 𝓞 K) = (hζ.unit'⁻¹ : (𝓞 K)ˣ) :=
    congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) (unitsComplexConj_zeta157 hζ)
  have hηreal' :
      NumberField.IsCMField.ringOfIntegersComplexConj K (η : 𝓞 K) = η :=
    congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) hηreal
  have hminus :
      s.omega + (hζ.unit'⁻¹ : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit'⁻¹ : (𝓞 K)ˣ)) * η * ρminus ^ 157 := by
    have hc := congrArg
      (NumberField.IsCMField.ringOfIntegersComplexConj K) hone
    simp only [map_add, map_mul, map_sub, map_one, map_pow,
      hs.1, hs.2.1, hconjζ, hηreal'] at hc
    simpa only [ρminus] using hc
  have hρnot : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ ρ := by
    intro hρ
    apply historicalZetaFactor_not_ramified157 hζ s hs
    rw [heq]
    exact dvd_mul_of_dvd_right
      (dvd_pow (n := 157) hρ (by norm_num)) _
  have hρminusNot : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ ρminus := by
    intro hρminus
    have hc := zeta_sub_one_pow_dvd_conj_of_dvd157 hζ 1 ρminus
      (by simpa only [pow_one] using hρminus)
    have hcc :
        NumberField.IsCMField.ringOfIntegersComplexConj K ρminus = ρ := by
      dsimp [ρminus]
      apply NumberField.RingOfIntegers.ext
      exact NumberField.IsCMField.complexConj_apply_apply K ρ
    apply hρnot
    simpa only [pow_one, hcc] using hc
  exact
    ⟨ρ, ρminus, η, hηreal, hone, hminus, rfl, hρnot, hρminusNot⟩

set_option maxRecDepth 50000 in
/-- Unconditional paired equation (8) at `a = 2,-2`, transported through
the primitive root `ζ²`. -/
theorem exists_historicalEquationEight_pair_two157_unconditional
    {ζ : K} (hζ : IsPrimitiveRoot ζ 157) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ∃ (ρtwo ρminus : 𝓞 K) (η : (𝓞 K)ˣ),
      NumberField.IsCMField.unitsComplexConj K η = η ∧
      s.omega + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * η * ρtwo ^ 157 ∧
      s.omega + ((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ) * s.theta =
        (1 - ((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ)) * η * ρminus ^ 157 ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K ρtwo = ρminus ∧
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ ρtwo ∧
      ¬ (hζ.unit' : 𝓞 K) - 1 ∣ ρminus := by
  let hζtwo := hζ.pow_of_coprime 2 (by norm_num)
  let stwo := historicalStateAtTwo157 hζ s
  have hstwo : RealSourceAdmissible hζtwo stwo := by
    simpa only [hζtwo, stwo] using
      historicalStateAtTwo_admissible157 hζ s hs
  obtain ⟨ρtwo, ρminus, η, hη, htwo, hminus, hconj,
      hρtwo, hρminus⟩ :=
    exists_historicalEquationEight_pair_one157_unconditional
      hζtwo stwo hstwo
  have hassoc :
      Associated ((hζ.unit' : 𝓞 K) - 1)
        ((hζtwo.unit' : 𝓞 K) - 1) := by
    simpa only [hζtwo, powTwoPrimitiveRoot_unit157 hζ,
      Units.val_pow_eq_pow_val] using
      hζ.unit'_coe.associated_sub_one_pow_sub_one_of_coprime
        (by norm_num : Nat.Coprime 2 157)
  refine ⟨ρtwo, ρminus, η, hη, ?_, ?_, hconj, ?_, ?_⟩
  · simpa only [stwo, historicalStateAtTwo157, hζtwo,
      powTwoPrimitiveRoot_unit157 hζ, Units.val_pow_eq_pow_val] using htwo
  · simpa only [stwo, historicalStateAtTwo157, hζtwo,
      powTwoPrimitiveRoot_unit157 hζ] using hminus
  · exact fun h ↦ hρtwo ((hassoc.dvd_iff_dvd_left).mp h)
  · exact fun h ↦ hρminus ((hassoc.dvd_iff_dvd_left).mp h)

end

end Fermat.OneHundredFiftySeven.TakagiHistorical157
