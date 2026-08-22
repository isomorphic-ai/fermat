import Fermat.Descent.GenericIrregular.SecondCase
import Fermat.Exponents.OneHundredFiftySeven.GenericChannels
import Fermat.Exponents.OneHundredFiftySeven.GenericLemmaTwo
import Fermat.Exponents.OneHundredFiftySeven.SinnottKummer

/-!
# Exponent 157 through the generic irregular second-case framework

This regression combines three independently checked inputs:

* the Sinnott--Kummer proof that `157` does not divide the plus class number;
* the finite diagonal-unit and logarithmic-derivative system;
* the two-channel axis-8 Faulhaber certificate.

The prime-generic assembly derives Vandiver's Lemma II internally and then
excludes the second case.  No exponent-specific second-case conclusion is
imported.
-/

open scoped NumberField

namespace Fermat.OneHundredFiftySeven.GenericSecondCase

noncomputable section

open Fermat.GenericIrregular.SecondCase

local instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {157} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 157) K (by norm_num)

/-- All exponent-dependent second-case inputs at `157`, packaged without a
Lemma-II or Fermat conclusion field. -/
def fixedSecondCaseCertificate157
    {ζ : K} (hζ : IsPrimitiveRoot ζ 157) :
    FixedSecondCaseCertificate K 157 2 where
  plusClassNondivisibility :=
    Fermat.OneHundredFiftySeven.SinnottKummer.not_dvd_classNumber hζ
  unitSystem :=
    Fermat.OneHundredFiftySeven.GenericLemmaTwo.lemmaTwoUnitSystem157
  channels :=
    Fermat.OneHundredFiftySeven.GenericChannels.fixedChannelCertificate

/-- Regression endpoint: the generic historical assembly excludes the
second case at `157`. -/
theorem secondCaseExcluded_oneHundredFiftySeven_generic
    {ζ : K} (hζ : IsPrimitiveRoot ζ 157) :
    Fermat.SecondCaseExcluded 157 :=
  secondCaseExcluded_of_certificate (by norm_num) hζ
    (fixedSecondCaseCertificate157 hζ)

end

end Fermat.OneHundredFiftySeven.GenericSecondCase
