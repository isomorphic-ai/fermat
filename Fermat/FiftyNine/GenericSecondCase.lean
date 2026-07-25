import Fermat.GenericIrregular.SecondCase
import Fermat.FiftyNine.GenericChannels
import Fermat.FiftyNine.GenericLemmaTwo
import Fermat.FiftyNine.SinnottKummer

/-!
# Exponent 59 through the generic irregular second-case framework

This regression combines three independently checked inputs:

* the Sinnott--Kummer proof that `59` does not divide the plus class number;
* the finite diagonal-unit and logarithmic-derivative system;
* the one-channel axis-8 Faulhaber certificate.

The prime-generic assembly then derives Vandiver's Lemma II and excludes the
second case.  No exponent-specific second-case conclusion is imported.
-/

open scoped NumberField

namespace Fermat.FiftyNine.GenericSecondCase

noncomputable section

open Fermat.GenericIrregular.SecondCase

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 59) K (by norm_num)

/-- All exponent-dependent second-case inputs at `59`, packaged without a
Lemma-II or Fermat conclusion field. -/
def fixedSecondCaseCertificate59
    {ζ : K} (hζ : IsPrimitiveRoot ζ 59) :
    FixedSecondCaseCertificate K 59 1 where
  plusClassNondivisibility :=
    Fermat.FiftyNine.SinnottKummer.not_dvd_classNumber hζ
  unitSystem :=
    Fermat.FiftyNine.GenericLemmaTwo.lemmaTwoUnitSystem59
  channels :=
    Fermat.FiftyNine.GenericChannels.fixedChannelCertificate

/-- Regression endpoint: the generic historical assembly excludes the
second case at `59`. -/
theorem secondCaseExcluded_fiftyNine_generic
    {ζ : K} (hζ : IsPrimitiveRoot ζ 59) :
    Fermat.SecondCaseExcluded 59 :=
  secondCaseExcluded_of_certificate (by norm_num) hζ
    (fixedSecondCaseCertificate59 hζ)

end

end Fermat.FiftyNine.GenericSecondCase
