import Fermat.Descent.GenericIrregular.SecondCase
import Fermat.Exponents.OneThousandThreeHundredEightyOne.GenericChannels
import Fermat.Exponents.OneThousandThreeHundredEightyOne.GenericLemmaTwo
import Fermat.Exponents.OneThousandThreeHundredEightyOne.SinnottKummer

/-!
# Exponent 1381 through the generic irregular second-case framework

This regression combines the Sinnott--Kummer plus-class theorem, the finite
diagonal-unit and derivative system, and the one-channel axis-8 Faulhaber
certificate.  The generic assembly derives Vandiver's Lemma II internally;
no exponent-specific second-case conclusion is imported.
-/

open scoped NumberField

namespace Fermat.OneThousandThreeHundredEightyOne.GenericSecondCase

noncomputable section

open Fermat.GenericIrregular.SecondCase

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1381} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 1381) K (by norm_num)

/-- All exponent-dependent second-case inputs at `1381`, packaged without a
Lemma-II or Fermat conclusion field. -/
def fixedSecondCaseCertificate1381
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1381) :
    FixedSecondCaseCertificate K 1381 1 where
  plusClassNondivisibility :=
    Fermat.OneThousandThreeHundredEightyOne.SinnottKummer.not_dvd_classNumber
      hζ
  unitSystem :=
    Fermat.OneThousandThreeHundredEightyOne.GenericLemmaTwo.lemmaTwoUnitSystem1381
  channels :=
    Fermat.OneThousandThreeHundredEightyOne.GenericChannels.fixedChannelCertificate

/-- Regression endpoint: the generic historical assembly excludes the
second case at `1381`. -/
theorem secondCaseExcluded_oneThousandThreeHundredEightyOne_generic
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1381) :
    Fermat.SecondCaseExcluded 1381 :=
  secondCaseExcluded_of_certificate (by norm_num) hζ
    (fixedSecondCaseCertificate1381 hζ)

end

end Fermat.OneThousandThreeHundredEightyOne.GenericSecondCase
