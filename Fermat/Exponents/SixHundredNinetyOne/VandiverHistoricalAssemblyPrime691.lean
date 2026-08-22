import Fermat.Descent.Irregular.VandiverHistoricalAssemblyPrime
import Fermat.Exponents.SixHundredNinetyOne.VandiverHistoricalAssembly691

/-!
# Regression endpoint for the prime-generic historical assembly at 691

The original exponent-specific formalization at `691` remains available.
This small module checks that the prime-generic Vandiver assembly produces
the same elimination boundary and can be substituted into the existing
second-case and final-FLT endpoint without changing their interfaces.
-/

namespace Fermat.SixHundredNinetyOne.VandiverHistorical

open Fermat.Irregular.VandiverHistoricalAssemblyPrime

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {691} ℚ K]

local instance : Fact (Nat.Prime 691) :=
  ⟨Fermat.SixHundredNinetyOne.prime_691⟩

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 691) K
    (by norm_num)

/-- The generic historical assembly reproduces the established
`RealPrincipalGeneratorElimination691` interface. -/
theorem realPrincipalGeneratorElimination691_via_generic
    {ζ : K} (hζ : IsPrimitiveRoot ζ 691) :
    RealPrincipalGeneratorElimination691 hζ :=
  realPrincipalGeneratorElimination_of_plusClass
    (p := 691) (by norm_num) hζ
    (Fermat.SixHundredNinetyOne.SinnottKummer.not_dvd_classNumber
      hζ)

end

end Fermat.SixHundredNinetyOne.VandiverHistorical

namespace Fermat.SixHundredNinetyOne

open scoped NumberField nonZeroDivisors Cyclotomic

/-- Regression of the complete historical second-case endpoint through the
prime-generic elimination. -/
theorem secondCaseExcluded_sixHundredNinetyOne_via_generic :
    Fermat.SecondCaseExcluded 691 := by
  letI : NeZero (691 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {691} ℚ (CyclotomicField 691 ℚ) :=
    CyclotomicField.isCyclotomicExtension 691 ℚ
  obtain ⟨zeta, hzeta⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 691 ℚ)
      (Set.mem_singleton 691) (by norm_num : 691 ≠ 0)
  intro a b c ha hb hc hgcd hdiv
  exact
    (VandiverHistorical.secondCaseExcluded_691_of_vandiverLemmaTwo
      (K := CyclotomicField 691 ℚ) (ζ := zeta)
      hzeta
      (VandiverHistorical.realPrincipalGeneratorElimination691_via_generic
        (K := CyclotomicField 691 ℚ) hzeta)
      (VandiverLemmaTwo.vandiverLemmaTwo_sixHundredNinetyOne
        (K := CyclotomicField 691 ℚ)))
      ha hb hc hgcd hdiv

/-- Regression of the complete FLT endpoint at `691` through the generic
historical elimination. -/
theorem holdsAt_sixHundredNinetyOne_via_generic :
    Fermat.HoldsAt 691 := by
  exact Fermat.holdsAt_of_auxiliaryPrime_of_secondCaseExcluded
    (by norm_num) (by norm_num) (by norm_num)
    noConsecutivePowers_691_11057 exponentNotPower_691_11057
    secondCaseExcluded_sixHundredNinetyOne_via_generic

end Fermat.SixHundredNinetyOne
