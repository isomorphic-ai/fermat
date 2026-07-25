import Fermat.GenericIrregular.SecondCase
import Fermat.SixHundredSeven.GenericChannels
import Fermat.SixHundredSeven.GenericLemmaTwo
import Fermat.SixHundredSeven.SinnottKummer

/-!
# Exponent 607 through the generic irregular second-case framework

This regression combines the Sinnott--Kummer plus-class calculation, the
finite diagonal-unit derivative system, and the one-channel axis-8
Faulhaber certificate.  The prime-generic assembly derives Vandiver's
Lemma II internally and excludes the second case.
-/

open scoped NumberField

namespace Fermat.SixHundredSeven.GenericSecondCase

noncomputable section

open Fermat.GenericIrregular.SecondCase

local instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {607} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 607) K (by norm_num)

/-- All exponent-dependent second-case inputs at `607`, with no Lemma-II
or Fermat conclusion stored as a field. -/
def fixedSecondCaseCertificate607
    {ζ : K} (hζ : IsPrimitiveRoot ζ 607) :
    FixedSecondCaseCertificate K 607 1 where
  plusClassNondivisibility :=
    Fermat.SixHundredSeven.SinnottKummer.not_dvd_classNumber hζ
  unitSystem :=
    Fermat.SixHundredSeven.GenericLemmaTwo.lemmaTwoUnitSystem607
  channels :=
    Fermat.SixHundredSeven.GenericChannels.fixedChannelCertificate

/-- Regression endpoint: the generic historical assembly excludes the
second case at `607`. -/
theorem secondCaseExcluded_sixHundredSeven_generic
    {ζ : K} (hζ : IsPrimitiveRoot ζ 607) :
    Fermat.SecondCaseExcluded 607 :=
  secondCaseExcluded_of_certificate (by norm_num) hζ
    (fixedSecondCaseCertificate607 hζ)

end

end Fermat.SixHundredSeven.GenericSecondCase
