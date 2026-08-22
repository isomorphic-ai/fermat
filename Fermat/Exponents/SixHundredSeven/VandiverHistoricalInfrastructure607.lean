import Fermat.Descent.Irregular.VandiverHistoricalPrime
import Fermat.Descent.Irregular.VandiverHistoricalStartPrime
import Fermat.Descent.Irregular.VandiverRealNormalizationPrime
import Fermat.Exponents.SixHundredSeven.VandiverData

/-!
# Historical-descent infrastructure at exponent 607

This file specializes the prime-generic parts of Vandiver's historical
descent to `607 = 2 * 303 + 1`.  Once the finite real-principal-generator
elimination and Vandiver's Lemma II are supplied, the generic descent and
the checked Bernoulli cube condition exclude the second case.
-/

namespace Fermat.SixHundredSeven.VandiverHistorical

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {607} ℚ K]

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 607) K (by norm_num)

/-- The exact finite, source-faithful elimination boundary at exponent
`607`. -/
abbrev RealPrincipalGeneratorElimination607 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 607) : Prop :=
  RealPrincipalGeneratorElimination hζ

/-- The inverse-of-two root-of-unity adjustment at
`607 = 2 * 303 + 1`. -/
def realGeneratorNormalizer607 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 607) :
    RealGeneratorNormalizer hζ :=
  Fermat.Irregular.VandiverRealNormalizationPrime.realGeneratorNormalizer
    (p := 607) (r := 303) (by norm_num) hζ

/-- Every `607`th-power presentation of a real unit admits a real root. -/
theorem realUnitRootNormalization607 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 607) :
    RealUnitRootNormalization hζ :=
  Fermat.Irregular.VandiverRealNormalizationPrime.realUnitRootNormalization
    (p := 607) (by norm_num) hζ

/-- A primitive rational second-case solution starts the historical
descent with exponent `m = 303`. -/
theorem secondCaseStartsHistoricalDescent_607 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 607) :
    SecondCaseStartsHistoricalDescent hζ (RealSourceAdmissible hζ) :=
  Fermat.Irregular.VandiverHistoricalStartPrime.secondCaseStartsHistoricalDescent
    (p := 607) (r := 303) (by norm_num) (by norm_num) hζ

/-- A finite elimination at `607` supplies the complete
equations-(7)--(10) reduction relation. -/
theorem equationsSevenToTenReduction_607
    {ζ : K} (hζ : IsPrimitiveRoot ζ 607)
    (heliminate : RealPrincipalGeneratorElimination607 hζ) :
    EquationsSevenToTenReduction hζ (RealSourceAdmissible hζ) :=
  equationsSevenToTenReduction hζ
    (realGeneratorNormalizer607 hζ)
    (realUnitRootNormalization607 hζ)
    heliminate

/-- The finite historical elimination and Kummer's deep unit conclusion
exclude the second case at exponent `607`. -/
theorem secondCaseExcluded_607_of_historical
    {ζ : K} (hζ : IsPrimitiveRoot ζ 607)
    (heliminate : RealPrincipalGeneratorElimination607 hζ)
    (hkummer :
      Fermat.Irregular.VandiverCriterion.KummerUnitPowerConclusion K 607) :
    Fermat.SecondCaseExcluded 607 :=
  secondCaseExcluded_of_historical_descent
    (p := 607) (by norm_num) hζ
    (RealSourceAdmissible hζ)
    (secondCaseStartsHistoricalDescent_607 hζ)
    (equationsSevenToTenReduction_607 hζ heliminate)
    hkummer

/-- Once the finite elimination is constructed, the checked Bernoulli
cube condition and Vandiver's Lemma II exclude the second case at
exponent `607`. -/
theorem secondCaseExcluded_607_of_vandiverLemmaTwo
    {ζ : K} (hζ : IsPrimitiveRoot ζ 607)
    (heliminate : RealPrincipalGeneratorElimination607 hζ)
    (hLemmaTwo :
      Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 607) :
    Fermat.SecondCaseExcluded 607 :=
  secondCaseExcluded_of_vandiverLemmaTwo
    (p := 607) (by norm_num) hζ
    (RealSourceAdmissible hζ)
    (secondCaseStartsHistoricalDescent_607 hζ)
    (equationsSevenToTenReduction_607 hζ heliminate)
    hLemmaTwo
    Fermat.SixHundredSeven.VandiverData.bernoulliCubeCondition_607

end

end Fermat.SixHundredSeven.VandiverHistorical
