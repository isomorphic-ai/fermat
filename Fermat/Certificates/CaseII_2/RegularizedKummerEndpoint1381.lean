import Fermat.Certificates.CaseII_2.BernoulliMomentCertificate1381
import Fermat.Core.Cases
import Fermat.Descent.KummerIso.SecondCase
import Fermat.Exponents.OneThousandThreeHundredEightyOne.FirstCase
import Fermat.Exponents.OneThousandThreeHundredEightyOne.GenericLemmaTwo
import Fermat.Exponents.OneThousandThreeHundredEightyOne.SinnottKummer

/-!
# Regularized Kummer endpoint from the 1381 moment receipt

This thin adapter feeds the compact Case-II.2 Bernoulli moment receipt into
the regularized Kummer unit-extraction route, then combines the resulting
second-case exclusion with the existing finite Sophie--Germain data.

It is a parallel endpoint.  Existing exponent modules are deliberately not
rewired here; switching all fixed-exponent consumers belongs to the later
certificate migration.
-/

open scoped NumberField

namespace Fermat.Certificates.CaseII_2.RegularizedKummerEndpoint1381

noncomputable section

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1381} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 1381) K (by norm_num)

/-- The regularized Kummer assembly excludes Case II at exponent `1381`
using the compact weighted-moment Bernoulli condition. -/
theorem secondCaseExcluded1381
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1381) :
    Fermat.SecondCaseExcluded 1381 :=
  Fermat.KummerIso.SecondCase.secondCaseExcluded_of_plusClass_of_unitSystem_of_bernoulliCubeCondition
    (by norm_num) hζ
    (Fermat.OneThousandThreeHundredEightyOne.SinnottKummer.not_dvd_classNumber
      hζ)
    Fermat.OneThousandThreeHundredEightyOne.GenericLemmaTwo.lemmaTwoUnitSystem1381
    Fermat.Certificates.CaseII_2.BernoulliMomentCertificate1381.bernoulliCubeCondition1381

private local instance : NeZero (1381 : ℚ) := ⟨by norm_num⟩

/-- Fermat's Last Theorem at exponent `1381` through the compact moment
Case-II.2 route. -/
theorem holdsAt1381 : Fermat.HoldsAt 1381 := by
  letI : IsCyclotomicExtension {1381} ℚ (CyclotomicField 1381 ℚ) :=
    CyclotomicField.isCyclotomicExtension 1381 ℚ
  letI : NumberField.IsCMField (CyclotomicField 1381 ℚ) :=
    IsCyclotomicExtension.IsCMField
      (p := 1381) (CyclotomicField 1381 ℚ) (by norm_num)
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 1381 ℚ)
      (Set.mem_singleton 1381) (by norm_num : 1381 ≠ 0)
  exact Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    Fermat.OneThousandThreeHundredEightyOne.prime_1381
    (by norm_num)
    Fermat.OneThousandThreeHundredEightyOne.prime_38669
    Fermat.OneThousandThreeHundredEightyOne.noConsecutivePowers_1381_38669
    Fermat.OneThousandThreeHundredEightyOne.exponentNotPower_1381_38669
    (secondCaseExcluded1381 hζ)

end

end Fermat.Certificates.CaseII_2.RegularizedKummerEndpoint1381
