import Fermat.GenericIrregular.SecondCase
import Fermat.SixtySeven.GenericChannels
import Fermat.SixtySeven.GenericLemmaTwo
import Fermat.SixtySeven.SinnottKummer

/-!
# Exponent 67 through the generic irregular second-case framework

This regression combines three independently checked inputs:

* the Sinnott--Kummer proof that `67` does not divide the plus class number;
* the finite diagonal-unit and logarithmic-derivative system;
* the one-channel axis-8 Faulhaber certificate.

The prime-generic assembly then derives Vandiver's Lemma II and excludes the
second case.  No exponent-specific second-case conclusion is imported.
-/

open scoped NumberField

namespace Fermat.SixtySeven.GenericSecondCase

noncomputable section

open Fermat.GenericIrregular.SecondCase

local instance : Fact (Nat.Prime 67) :=
  ⟨Fermat.SixtySeven.prime_67⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {67} ℚ K]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 67) K (by norm_num)

/-- All exponent-dependent second-case inputs at `67`, packaged without a
Lemma-II or Fermat conclusion field. -/
def fixedSecondCaseCertificate67
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) :
    FixedSecondCaseCertificate K 67 1 where
  plusClassNondivisibility :=
    Fermat.SixtySeven.SinnottKummer.not_dvd_classNumber hζ
  unitSystem :=
    Fermat.SixtySeven.GenericLemmaTwo.lemmaTwoUnitSystem67
  channels :=
    Fermat.SixtySeven.GenericChannels.fixedChannelCertificate

/-- Regression endpoint: the generic historical assembly excludes the
second case at `67`. -/
theorem secondCaseExcluded_sixtySeven_generic
    {ζ : K} (hζ : IsPrimitiveRoot ζ 67) :
    Fermat.SecondCaseExcluded 67 :=
  secondCaseExcluded_of_certificate (by norm_num) hζ
    (fixedSecondCaseCertificate67 hζ)

end

end Fermat.SixtySeven.GenericSecondCase
