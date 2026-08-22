import Fermat.Descent.GenericIrregular.SecondCase
import Fermat.Exponents.FourHundredNinetyOne.GenericChannels
import Fermat.Exponents.FourHundredNinetyOne.GenericLemmaTwo
import Fermat.Exponents.FourHundredNinetyOne.SinnottKummer

/-!
# Exponent 491 through the generic irregular second-case framework

This regression combines three independently checked inputs:

* the Sinnott--Kummer proof that `491` does not divide the plus class number;
* the finite diagonal-unit and logarithmic-derivative system;
* the three-channel axis-8 Faulhaber certificate.

The prime-generic assembly derives Vandiver's Lemma II internally and then
excludes the second case.  No exponent-specific second-case conclusion is
imported.
-/

open scoped NumberField

namespace Fermat.FourHundredNinetyOne.GenericSecondCase

noncomputable section

open Fermat.GenericIrregular.SecondCase

local instance : Fact (Nat.Prime 491) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {491} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 491) K (by norm_num)

/-- All exponent-dependent second-case inputs at `491`, packaged without a
Lemma-II or Fermat conclusion field. -/
def fixedSecondCaseCertificate491
    {ζ : K} (hζ : IsPrimitiveRoot ζ 491) :
    FixedSecondCaseCertificate K 491 3 where
  plusClassNondivisibility :=
    Fermat.FourHundredNinetyOne.SinnottKummer.not_dvd_classNumber hζ
  unitSystem :=
    Fermat.FourHundredNinetyOne.GenericLemmaTwo.lemmaTwoUnitSystem491
  channels :=
    Fermat.FourHundredNinetyOne.GenericChannels.fixedChannelCertificate

/-- Regression endpoint: the generic historical assembly excludes the
second case at `491`. -/
theorem secondCaseExcluded_fourHundredNinetyOne_generic
    {ζ : K} (hζ : IsPrimitiveRoot ζ 491) :
    Fermat.SecondCaseExcluded 491 :=
  secondCaseExcluded_of_certificate (by norm_num) hζ
    (fixedSecondCaseCertificate491 hζ)

end

end Fermat.FourHundredNinetyOne.GenericSecondCase
