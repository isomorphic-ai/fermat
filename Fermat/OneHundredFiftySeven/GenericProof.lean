import Fermat.GenericIrregular.FixedExponent
import Fermat.OneHundredFiftySeven.FirstCase
import Fermat.OneHundredFiftySeven.GenericSecondCase

/-!
# FLT at exponent 157 through the generic fixed-exponent interface

This file is the end-to-end regression: the concrete Sophie--Germain,
plus-class, diagonal-unit, derivative, and two-channel axis-8 data are
packaged as a `FixedIrregularCertificate`; the prime-generic theorem alone
turns that certificate into `Fermat.HoldsAt 157`.
-/

open scoped NumberField

namespace Fermat.OneHundredFiftySeven.GenericProof

noncomputable section

open Fermat.GenericIrregular.FixedExponent

local instance : Fact (Nat.Prime 157) :=
  ⟨Fermat.OneHundredFiftySeven.prime_157⟩

/-- The finite Sophie--Germain residue certificate at auxiliary prime 1571. -/
def sophieGermainCertificate157 : SophieGermainCertificate 157 where
  auxiliaryPrime := 1571
  auxiliaryPrime_isPrime :=
    Fermat.OneHundredFiftySeven.prime_1571
  noConsecutivePowers :=
    Fermat.OneHundredFiftySeven.noConsecutivePowers_157_1571
  exponentNotPower :=
    Fermat.OneHundredFiftySeven.exponentNotPower_157_1571

/-- The complete fixed-exponent certificate at `157`.

A primitive root is chosen only to extract the root-independent
plus-class-number statement from the concrete Sinnott--Kummer theorem.
Every unit and derivative field remains uniform in the later root chosen
by the generic assembly. -/
def fixedIrregularCertificate157 :
    FixedIrregularCertificate 157 2 := by
  letI : NeZero (157 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {157} ℚ (CyclotomicField 157 ℚ) :=
    CyclotomicField.isCyclotomicExtension 157 ℚ
  have hroot :
      ∃ ζ : CyclotomicField 157 ℚ, IsPrimitiveRoot ζ 157 :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 157 ℚ)
      (Set.mem_singleton 157) (by norm_num : 157 ≠ 0)
  let ζ := Classical.choose hroot
  have hζ : IsPrimitiveRoot ζ 157 :=
    Classical.choose_spec hroot
  exact
    { exponent_atLeastFive := by norm_num
      sophieGermain := sophieGermainCertificate157
      secondCase :=
        Fermat.OneHundredFiftySeven.GenericSecondCase.fixedSecondCaseCertificate157
          hζ }

/-- Fermat's Last Theorem at exponent `157`, obtained solely through the
new prime-generic fixed-exponent theorem. -/
theorem holdsAt_oneHundredFiftySeven_generic : Fermat.HoldsAt 157 :=
  holdsAt_of_certificate fixedIrregularCertificate157

end

end Fermat.OneHundredFiftySeven.GenericProof
