import Fermat.Descent.GenericIrregular.SecondCase
import Fermat.Exponents.FiveHundredEightySeven.GenericChannels
import Fermat.Exponents.FiveHundredEightySeven.GenericLemmaTwo
import Fermat.Exponents.FiveHundredEightySeven.SinnottKummer

/-!
# Exponent 587 through the generic irregular second-case framework

This regression combines the Sinnott--Kummer plus-class theorem, the finite
diagonal-unit and derivative system, and the two-channel axis-8 Faulhaber
certificate.  The generic assembly derives Vandiver's Lemma II internally;
no exponent-specific second-case conclusion is imported.
-/

open scoped NumberField

namespace Fermat.FiveHundredEightySeven.GenericSecondCase

noncomputable section

open Fermat.GenericIrregular.SecondCase

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {587} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 587) K (by norm_num)

/-- All exponent-dependent second-case inputs at `587`, packaged without a
Lemma-II or Fermat conclusion field. -/
def fixedSecondCaseCertificate587
    {ζ : K} (hζ : IsPrimitiveRoot ζ 587) :
    FixedSecondCaseCertificate K 587 2 where
  plusClassNondivisibility :=
    Fermat.FiveHundredEightySeven.SinnottKummer.not_dvd_classNumber hζ
  unitSystem :=
    Fermat.FiveHundredEightySeven.GenericLemmaTwo.lemmaTwoUnitSystem587
  channels :=
    Fermat.FiveHundredEightySeven.GenericChannels.fixedChannelCertificate

/-- Regression endpoint: the generic historical assembly excludes the
second case at `587`. -/
theorem secondCaseExcluded_fiveHundredEightySeven_generic
    {ζ : K} (hζ : IsPrimitiveRoot ζ 587) :
    Fermat.SecondCaseExcluded 587 :=
  secondCaseExcluded_of_certificate (by norm_num) hζ
    (fixedSecondCaseCertificate587 hζ)

end

end Fermat.FiveHundredEightySeven.GenericSecondCase
