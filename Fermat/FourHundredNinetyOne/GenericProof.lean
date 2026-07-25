import Fermat.GenericIrregular.FixedExponent
import Fermat.FourHundredNinetyOne.FirstCase
import Fermat.FourHundredNinetyOne.GenericSecondCase

/-!
# FLT at exponent 491 through the generic fixed-exponent interface

This file is the end-to-end regression: the concrete Sophie--Germain,
plus-class, diagonal-unit, derivative, and three-channel axis-8 data are
packaged as a `FixedIrregularCertificate`; the prime-generic theorem alone
turns that certificate into `Fermat.HoldsAt 491`.
-/

open scoped NumberField

namespace Fermat.FourHundredNinetyOne.GenericProof

noncomputable section

open Fermat.GenericIrregular.FixedExponent

local instance : Fact (Nat.Prime 491) :=
  ⟨Fermat.FourHundredNinetyOne.prime_491⟩

/-- The finite Sophie--Germain residue certificate at auxiliary prime 983. -/
def sophieGermainCertificate491 : SophieGermainCertificate 491 where
  auxiliaryPrime := 983
  auxiliaryPrime_isPrime :=
    Fermat.FourHundredNinetyOne.prime_983
  noConsecutivePowers :=
    Fermat.FourHundredNinetyOne.noConsecutivePowers_491_983
  exponentNotPower :=
    Fermat.FourHundredNinetyOne.exponentNotPower_491_983

/-- The complete fixed-exponent certificate at `491`.

A primitive root is chosen only to extract the root-independent
plus-class-number statement from the concrete Sinnott--Kummer theorem.
Every unit and derivative field remains uniform in the later root chosen
by the generic assembly. -/
def fixedIrregularCertificate491 :
    FixedIrregularCertificate 491 3 := by
  letI : NeZero (491 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {491} ℚ (CyclotomicField 491 ℚ) :=
    CyclotomicField.isCyclotomicExtension 491 ℚ
  have hroot :
      ∃ ζ : CyclotomicField 491 ℚ, IsPrimitiveRoot ζ 491 :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 491 ℚ)
      (Set.mem_singleton 491) (by norm_num : 491 ≠ 0)
  let ζ := Classical.choose hroot
  have hζ : IsPrimitiveRoot ζ 491 :=
    Classical.choose_spec hroot
  exact
    { exponent_atLeastFive := by norm_num
      sophieGermain := sophieGermainCertificate491
      secondCase :=
        Fermat.FourHundredNinetyOne.GenericSecondCase.fixedSecondCaseCertificate491
          hζ }

/-- Fermat's Last Theorem at exponent `491`, obtained solely through the
new prime-generic fixed-exponent theorem. -/
theorem holdsAt_fourHundredNinetyOne_generic : Fermat.HoldsAt 491 :=
  holdsAt_of_certificate fixedIrregularCertificate491

end

end Fermat.FourHundredNinetyOne.GenericProof
