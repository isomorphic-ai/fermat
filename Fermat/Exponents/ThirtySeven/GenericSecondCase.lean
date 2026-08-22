import Fermat.Descent.GenericIrregular.SecondCase
import Fermat.Exponents.ThirtySeven.GenericChannels
import Fermat.Exponents.ThirtySeven.GenericLemmaTwo
import Fermat.Exponents.ThirtySeven.SinnottKummer

/-!
# Exponent 37 through the generic irregular second-case framework

This is the first concrete regression for `GenericIrregular`.  It combines
three independently checked inputs:

* the Sinnott--Kummer proof that `37` does not divide the plus class number;
* the finite diagonal-unit and logarithmic-derivative system;
* the one-channel axis-8 Faulhaber certificate.

The prime-generic assembly then derives Vandiver's Lemma II and excludes the
second case.  No exponent-specific second-case conclusion is imported.
-/

open scoped NumberField

namespace Fermat.ThirtySeven.GenericSecondCase

noncomputable section

open Fermat.GenericIrregular.SecondCase

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 37) K (by norm_num)

/-- All exponent-dependent second-case inputs at `37`, packaged without a
Lemma-II or Fermat conclusion field. -/
def fixedSecondCaseCertificate37
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) :
    FixedSecondCaseCertificate K 37 1 where
  plusClassNondivisibility :=
    Fermat.ThirtySeven.SinnottKummer.not_dvd_classNumber hζ
  unitSystem :=
    Fermat.ThirtySeven.GenericLemmaTwo.lemmaTwoUnitSystem37
  channels :=
    Fermat.ThirtySeven.GenericChannels.fixedChannelCertificate

/-- Regression endpoint: the generic historical assembly excludes the
second case at `37`. -/
theorem secondCaseExcluded_thirtySeven_generic
    {ζ : K} (hζ : IsPrimitiveRoot ζ 37) :
    Fermat.SecondCaseExcluded 37 :=
  secondCaseExcluded_of_certificate (by norm_num) hζ
    (fixedSecondCaseCertificate37 hζ)

end

end Fermat.ThirtySeven.GenericSecondCase
