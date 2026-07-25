import Fermat.GenericIrregular.SecondCase
import Fermat.SixHundredNinetyOne.GenericChannels
import Fermat.SixHundredNinetyOne.GenericLemmaTwo
import Fermat.SixHundredNinetyOne.SinnottKummer

/-!
# Exponent 691 through the generic irregular second-case framework

This regression combines the Sinnott--Kummer plus-class calculation, the
finite diagonal-unit derivative system, and the two-channel axis-8
Faulhaber certificate.  The prime-generic assembly derives Vandiver's
Lemma II internally and excludes the second case.
-/

open scoped NumberField

namespace Fermat.SixHundredNinetyOne.GenericSecondCase

noncomputable section

open Fermat.GenericIrregular.SecondCase

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {691} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 691) K (by norm_num)

/-- All exponent-dependent second-case inputs at `691`, with no Lemma-II
or Fermat conclusion stored as a field. -/
def fixedSecondCaseCertificate691
    {ζ : K} (hζ : IsPrimitiveRoot ζ 691) :
    FixedSecondCaseCertificate K 691 2 where
  plusClassNondivisibility :=
    Fermat.SixHundredNinetyOne.SinnottKummer.not_dvd_classNumber hζ
  unitSystem :=
    Fermat.SixHundredNinetyOne.GenericLemmaTwo.lemmaTwoUnitSystem691
  channels :=
    Fermat.SixHundredNinetyOne.GenericChannels.fixedChannelCertificate

/-- Regression endpoint: the generic historical assembly excludes the
second case at `691`. -/
theorem secondCaseExcluded_sixHundredNinetyOne_generic
    {ζ : K} (hζ : IsPrimitiveRoot ζ 691) :
    Fermat.SecondCaseExcluded 691 :=
  secondCaseExcluded_of_certificate (by norm_num) hζ
    (fixedSecondCaseCertificate691 hζ)

end

end Fermat.SixHundredNinetyOne.GenericSecondCase
