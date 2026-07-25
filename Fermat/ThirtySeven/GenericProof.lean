import Fermat.GenericIrregular.FixedExponent
import Fermat.ThirtySeven.FirstCase
import Fermat.ThirtySeven.GenericSecondCase

/-!
# FLT at exponent 37 through the generic fixed-exponent interface

This file is the end-to-end regression: the concrete Sophie--Germain,
plus-class, diagonal-unit, derivative, and axis-8 channel data are packaged
as a `FixedIrregularCertificate`; the prime-generic theorem alone turns that
certificate into `Fermat.HoldsAt 37`.
-/

open scoped NumberField

namespace Fermat.ThirtySeven.GenericProof

noncomputable section

open Fermat.GenericIrregular.FixedExponent

local instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- The finite Sophie--Germain residue certificate at auxiliary prime 149. -/
def sophieGermainCertificate37 : SophieGermainCertificate 37 where
  auxiliaryPrime := 149
  auxiliaryPrime_isPrime := by
    norm_num
  noConsecutivePowers :=
    Fermat.ThirtySeven.noConsecutivePowers_37_149
  exponentNotPower :=
    Fermat.ThirtySeven.exponentNotPower_37_149

/-- The complete fixed-exponent certificate at `37`.

A primitive root is chosen only to extract the root-independent
plus-class-number statement from the concrete Sinnott--Kummer theorem.
Every unit and derivative field remains uniform in the later root chosen
by the generic assembly. -/
def fixedIrregularCertificate37 :
    FixedIrregularCertificate 37 1 := by
  letI : NeZero (37 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ) :=
    CyclotomicField.isCyclotomicExtension 37 ℚ
  have hroot :
      ∃ ζ : CyclotomicField 37 ℚ, IsPrimitiveRoot ζ 37 :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 37 ℚ)
      (Set.mem_singleton 37) (by norm_num : 37 ≠ 0)
  let ζ := Classical.choose hroot
  have hζ : IsPrimitiveRoot ζ 37 :=
    Classical.choose_spec hroot
  exact
    { exponent_atLeastFive := by norm_num
      sophieGermain := sophieGermainCertificate37
      secondCase :=
        Fermat.ThirtySeven.GenericSecondCase.fixedSecondCaseCertificate37
          hζ }

/-- Fermat's Last Theorem at exponent `37`, obtained solely through the
new prime-generic fixed-exponent theorem. -/
theorem holdsAt_thirtySeven_generic : Fermat.HoldsAt 37 :=
  holdsAt_of_certificate fixedIrregularCertificate37

end

end Fermat.ThirtySeven.GenericProof
