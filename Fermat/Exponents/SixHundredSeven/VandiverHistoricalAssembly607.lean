import Fermat.Descent.Irregular.VandiverHistoricalAssemblyPrime
import Fermat.Exponents.SixHundredSeven.SinnottKummer
import Fermat.Exponents.SixHundredSeven.VandiverHistoricalInfrastructure607
import Fermat.Exponents.SixHundredSeven.VandiverLemmaTwo
import Fermat.Exponents.SixHundredSeven.VandiverData
import Fermat.Exponents.SixHundredSeven.FirstCase
import Fermat.Core.Cases

/-!
# Historical elimination at exponent 607

The prime-generic historical assembly turns the checked Sinnott--Kummer
plus-class certificate into the exact real-principal-generator
elimination.  The exponent-specific diagonal-unit calculation supplies
Vandiver's Lemma II, completing the second case.
-/

namespace Fermat.SixHundredSeven.VandiverHistorical

open Fermat.Irregular.VandiverHistoricalAssemblyPrime

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {607} ℚ K]

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 607) K (by norm_num)

/-- The source-faithful real-principal-generator elimination at exponent
`607`.  Its only exponent-specific finite dependency is the checked
Sinnott--Kummer plus-class certificate. -/
theorem realPrincipalGeneratorElimination607
    {ζ : K} (hζ : IsPrimitiveRoot ζ 607) :
    RealPrincipalGeneratorElimination607 hζ :=
  realPrincipalGeneratorElimination_of_plusClass
    (p := 607) (by norm_num) hζ
    (Fermat.SixHundredSeven.SinnottKummer.not_dvd_classNumber hζ)

end

end Fermat.SixHundredSeven.VandiverHistorical

namespace Fermat.SixHundredSeven

open scoped NumberField nonZeroDivisors Cyclotomic

/-- Vandiver's historical proof excludes the second case at exponent
`607`, with the cyclotomic field and primitive root chosen canonically. -/
theorem secondCaseExcluded_sixHundredSeven :
    Fermat.SecondCaseExcluded 607 := by
  letI : NeZero (607 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {607} ℚ (CyclotomicField 607 ℚ) :=
    CyclotomicField.isCyclotomicExtension 607 ℚ
  obtain ⟨zeta, hzeta⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 607 ℚ)
      (Set.mem_singleton 607) (by norm_num : 607 ≠ 0)
  intro a b c ha hb hc hgcd hdiv
  exact
    (VandiverHistorical.secondCaseExcluded_607_of_vandiverLemmaTwo
      (K := CyclotomicField 607 ℚ) (ζ := zeta)
      hzeta
      (VandiverHistorical.realPrincipalGeneratorElimination607
        (K := CyclotomicField 607 ℚ) hzeta)
      (VandiverLemmaTwo.vandiverLemmaTwo_sixHundredSeven
        (K := CyclotomicField 607 ℚ)))
      ha hb hc hgcd hdiv

/-- Fermat's Last Theorem at exponent `607`. -/
theorem holdsAt_sixHundredSeven :
    Fermat.HoldsAt 607 := by
  exact Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    prime_607 (by norm_num) prime_20639
    noConsecutivePowers_607_20639 exponentNotPower_607_20639
    secondCaseExcluded_sixHundredSeven

/-- Numeric-name alias for campaign consumers. -/
theorem holdsAt_607 : Fermat.HoldsAt 607 :=
  holdsAt_sixHundredSeven

end Fermat.SixHundredSeven
