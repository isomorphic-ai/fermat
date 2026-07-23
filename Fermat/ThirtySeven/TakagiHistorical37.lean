import Fermat.Irregular.TakagiReflection37
import Fermat.ThirtySeven.VandiverHistorical

/-!
# Unconditional Takagi--Furtwängler step in Vandiver's historical proof

The universal predicate `LemmaOne K 37` is stronger than the instance
used by Vandiver's equation (7a).  The historical radicand is the explicit
conjugate pair

`q₊ * conj(q₊)^36`.

The conjugation-fixed Kummer extension constructed in
`TakagiReflection37` therefore proves the required historical equation
directly, without taking the universal class-field-theoretic predicate as
an input.
-/

open scoped NumberField

namespace Fermat.ThirtySeven.TakagiHistorical37

noncomputable section

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.TakagiReflection37
open Fermat.ThirtySeven.VandiverHistorical

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 37) K (by norm_num)

set_option maxRecDepth 3000 in
/-- Vandiver's historical equation (7a), now discharged by the explicit
conjugation-fixed unramified Kummer extension and Hilbert 94. -/
theorem exists_historicalEquationSevenA37_unconditional
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ∃ r : 𝓞 K,
      historicalZetaFactorIdeal37 hζ s *
          historicalInverseZetaFactorIdeal37 hζ s ^ 36 =
        Ideal.span {r} := by
  exact exists_conjugatePairEquationSevenAGenerator37 hζ
    (historicalZetaFactorIdeal37 hζ s)
    (historicalInverseZetaFactorIdeal37 hζ s)
    (historicalZetaFactor37 hζ s)
    (normalizedHistoricalInverseZetaFactor37 hζ s)
    (historicalZetaFactorIdeal_pow37 hζ s)
    (historicalInverseZetaFactorIdeal_pow37 hζ s)
    (ringOfIntegersComplexConj_historicalZetaFactor37 hζ s hs)
    (historicalConjugateFactorProduct_isKummerPrimary37 hζ s hs)

set_option maxRecDepth 3000 in
/-- Vandiver's historical equation (8), with the former Lemma-1 premise
removed.  Equation (7a) is supplied above; equation (7d), nonvanishing,
and the Bézout ideal calculation are the existing kernel-checked
historical results. -/
theorem exists_historicalEquationEight37_unconditional
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) (s : HistoricalState hζ)
    (hs : RealSourceAdmissible hζ s) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ),
      historicalZetaFactorIdeal37 hζ s = Ideal.span {ρ} ∧
      historicalZetaFactor37 hζ s = η * ρ ^ 37 := by
  obtain ⟨r, hsevenA⟩ :=
    exists_historicalEquationSevenA37_unconditional hζ s hs
  obtain ⟨t, hsevenD⟩ :=
    exists_historicalEquationSevenD37 hζ s hs
  obtain ⟨hI0, hJ0⟩ :=
    historicalFactorIdeals_ne_zero37 hζ s hs
  exact exists_equationEight_of_sevenASevenD37
    (historicalZetaFactorIdeal37 hζ s)
    (historicalInverseZetaFactorIdeal37 hζ s)
    (historicalZetaFactor37 hζ s)
    (normalizedHistoricalInverseZetaFactor37 hζ s)
    r t hI0 hJ0
    (historicalZetaFactorIdeal_pow37 hζ s)
    (historicalInverseZetaFactorIdeal_pow37 hζ s)
    hsevenA hsevenD

end

end Fermat.ThirtySeven.TakagiHistorical37
