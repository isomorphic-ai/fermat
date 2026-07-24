import Fermat.Irregular.VandiverHistoricalAssemblyPrime
import Fermat.OneThousandThreeHundredEightyOne.SinnottKummer
import Fermat.OneThousandThreeHundredEightyOne.VandiverHistoricalInfrastructure1381
import Fermat.OneThousandThreeHundredEightyOne.VandiverLemmaTwoAssembly1381
import Fermat.OneThousandThreeHundredEightyOne.VandiverPositiveRelationDerivative1381
import Fermat.OneThousandThreeHundredEightyOne.VandiverData
import Fermat.OneThousandThreeHundredEightyOne.FirstCase
import Fermat.Cases

/-!
# Historical elimination at exponent 1381

The generic historical assembly reduces this endpoint to the checked
Sinnott--Kummer plus-class certificate.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverHistorical

open Fermat.Irregular.VandiverHistoricalAssemblyPrime

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1381} ℚ K]

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 1381) K (by norm_num)

/-- The source-faithful real-principal-generator elimination at exponent
`1381`. -/
theorem realPrincipalGeneratorElimination1381
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1381) :
    RealPrincipalGeneratorElimination1381 hζ :=
  realPrincipalGeneratorElimination_of_plusClass
    (p := 1381) (by norm_num) hζ
    (Fermat.OneThousandThreeHundredEightyOne.SinnottKummer.not_dvd_classNumber
      hζ)

end

end Fermat.OneThousandThreeHundredEightyOne.VandiverHistorical

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverLemmaTwo

open scoped NumberField

noncomputable section

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1381} ℚ K]

/-- Vandiver's exact Lemma II alternative at exponent `1381`, assembled
from the checked positive-relation derivative congruences. -/
theorem vandiverLemmaTwo_oneThousandThreeHundredEightyOne :
    Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 1381 := by
  apply
    Fermat.OneThousandThreeHundredEightyOne.VandiverLemmaTwoAssembly.vandiverLemmaTwo_of_positiveRelationDerivativeCongruences1381
  intro zeta hzeta
  exact
    Fermat.OneThousandThreeHundredEightyOne.VandiverPositiveRelationDerivative.positiveRelationDerivativeCongruences1381
      hzeta

end

end Fermat.OneThousandThreeHundredEightyOne.VandiverLemmaTwo

namespace Fermat.OneThousandThreeHundredEightyOne

open scoped NumberField nonZeroDivisors Cyclotomic

/-- Vandiver's historical proof excludes the second case at exponent
`1381`, with the cyclotomic field and primitive root chosen canonically. -/
theorem secondCaseExcluded_oneThousandThreeHundredEightyOne :
    Fermat.SecondCaseExcluded 1381 := by
  letI : NeZero (1381 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {1381} ℚ (CyclotomicField 1381 ℚ) :=
    CyclotomicField.isCyclotomicExtension 1381 ℚ
  obtain ⟨zeta, hzeta⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 1381 ℚ)
      (Set.mem_singleton 1381) (by norm_num : 1381 ≠ 0)
  intro a b c ha hb hc hgcd hdiv
  exact
    (VandiverHistorical.secondCaseExcluded_1381_of_vandiverLemmaTwo
      (K := CyclotomicField 1381 ℚ) (ζ := zeta)
      hzeta
      (VandiverHistorical.realPrincipalGeneratorElimination1381
        (K := CyclotomicField 1381 ℚ) hzeta)
      (VandiverLemmaTwo.vandiverLemmaTwo_oneThousandThreeHundredEightyOne
        (K := CyclotomicField 1381 ℚ)))
      ha hb hc hgcd hdiv

/-- Fermat's Last Theorem at exponent `1381`. -/
theorem holdsAt_oneThousandThreeHundredEightyOne :
    Fermat.HoldsAt 1381 := by
  exact Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    prime_1381 (by norm_num) prime_38669
    noConsecutivePowers_1381_38669 exponentNotPower_1381_38669
    secondCaseExcluded_oneThousandThreeHundredEightyOne

end Fermat.OneThousandThreeHundredEightyOne
