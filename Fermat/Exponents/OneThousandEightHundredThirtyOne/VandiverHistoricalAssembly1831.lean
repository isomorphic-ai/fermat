import Fermat.Descent.Irregular.VandiverHistoricalAssemblyPrime
import Fermat.Exponents.OneThousandEightHundredThirtyOne.SinnottKummer
import Fermat.Exponents.OneThousandEightHundredThirtyOne.VandiverHistoricalInfrastructure1831
import Fermat.Exponents.OneThousandEightHundredThirtyOne.VandiverLemmaTwo
import Fermat.Exponents.OneThousandEightHundredThirtyOne.VandiverData
import Fermat.Exponents.OneThousandEightHundredThirtyOne.FirstCase
import Fermat.Core.Cases

/-!
# Historical elimination at exponent 1831

The generic historical assembly reduces this endpoint to the single
future finite input
`SinnottKummer.not_dvd_classNumber`.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.VandiverHistorical

open Fermat.Irregular.VandiverHistoricalAssemblyPrime

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 1831) K (by norm_num)

/-- The source-faithful real-principal-generator elimination at exponent
`1831`. Its only exponent-specific finite dependency is
`SinnottKummer.not_dvd_classNumber`. -/
theorem realPrincipalGeneratorElimination1831
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1831) :
    RealPrincipalGeneratorElimination1831 hζ :=
  realPrincipalGeneratorElimination_of_plusClass
    (p := 1831) (by norm_num) hζ
    (Fermat.OneThousandEightHundredThirtyOne.SinnottKummer.not_dvd_classNumber
      hζ)

end

end Fermat.OneThousandEightHundredThirtyOne.VandiverHistorical

namespace Fermat.OneThousandEightHundredThirtyOne

open scoped NumberField nonZeroDivisors Cyclotomic

/-- Vandiver's historical proof excludes the second case at exponent
`1831`, with the cyclotomic field and primitive root chosen canonically. -/
theorem secondCaseExcluded_oneThousandEightHundredThirtyOne :
    Fermat.SecondCaseExcluded 1831 := by
  letI : NeZero (1831 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {1831} ℚ (CyclotomicField 1831 ℚ) :=
    CyclotomicField.isCyclotomicExtension 1831 ℚ
  obtain ⟨zeta, hzeta⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 1831 ℚ)
      (Set.mem_singleton 1831) (by norm_num : 1831 ≠ 0)
  intro a b c ha hb hc hgcd hdiv
  exact
    (VandiverHistorical.secondCaseExcluded_1831_of_vandiverLemmaTwo
      (K := CyclotomicField 1831 ℚ) (ζ := zeta)
      hzeta
      (VandiverHistorical.realPrincipalGeneratorElimination1831
        (K := CyclotomicField 1831 ℚ) hzeta)
      (VandiverLemmaTwo.vandiverLemmaTwo_oneThousandEightHundredThirtyOne
        (K := CyclotomicField 1831 ℚ)))
      ha hb hc hgcd hdiv

/-- Fermat's Last Theorem at exponent `1831`. -/
theorem holdsAt_oneThousandEightHundredThirtyOne :
    Fermat.HoldsAt 1831 := by
  exact Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    prime_1831 (by norm_num) prime_358877
    noConsecutivePowers_1831_358877 exponentNotPower_1831_358877
    secondCaseExcluded_oneThousandEightHundredThirtyOne

end Fermat.OneThousandEightHundredThirtyOne
