import Fermat.GenericIrregular.FixedExponent
import Fermat.SixtySeven.FirstCase
import Fermat.SixtySeven.GenericSecondCase

/-!
# FLT at exponent 67 through the generic fixed-exponent interface

This file is the end-to-end regression: the concrete plus-class,
diagonal-unit, derivative, and axis-8 channel data are packaged as a
`FixedIrregularCertificate`, the fixed-second-case input to the
prime-generic theorem.  That theorem combines it with the generic
proof-producing Sophie--Germain search to obtain `Fermat.HoldsAt 67`.
The explicit concrete Sophie--Germain certificate below is an independent
finite-check regression; the endpoint does not consume it.
-/

open scoped NumberField

namespace Fermat.SixtySeven.GenericProof

noncomputable section

open Fermat.GenericIrregular.FixedExponent

local instance : Fact (Nat.Prime 67) :=
  ⟨Fermat.SixtySeven.prime_67⟩

/-- The finite Sophie--Germain residue certificate at auxiliary prime 269. -/
def sophieGermainCertificate67 : SophieGermainCertificate 67 where
  auxiliaryPrime := 269
  auxiliaryPrime_isPrime :=
    Fermat.SixtySeven.prime_269
  noConsecutivePowers :=
    Fermat.SixtySeven.noConsecutivePowers_67_269
  exponentNotPower :=
    Fermat.SixtySeven.exponentNotPower_67_269

/-- The fixed-second-case certificate at `67`.

A primitive root is chosen only to extract the root-independent
plus-class-number statement from the concrete Sinnott--Kummer theorem.
Every unit and derivative field remains uniform in the later root chosen
by the generic assembly.  Case I is supplied separately by the generic
search. -/
def fixedIrregularCertificate67 :
    FixedIrregularCertificate 67 1 := by
  letI : NeZero (67 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {67} ℚ (CyclotomicField 67 ℚ) :=
    CyclotomicField.isCyclotomicExtension 67 ℚ
  have hroot :
      ∃ ζ : CyclotomicField 67 ℚ, IsPrimitiveRoot ζ 67 :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 67 ℚ)
      (Set.mem_singleton 67) (by norm_num : 67 ≠ 0)
  let ζ := Classical.choose hroot
  have hζ : IsPrimitiveRoot ζ 67 :=
    Classical.choose_spec hroot
  exact
    { exponent_atLeastFive := by norm_num
      secondCase :=
        Fermat.SixtySeven.GenericSecondCase.fixedSecondCaseCertificate67
          hζ }

/-- Fermat's Last Theorem at exponent `67`, obtained solely through the
new prime-generic fixed-exponent theorem. -/
theorem holdsAt_sixtySeven_generic : Fermat.HoldsAt 67 :=
  holdsAt_of_certificate fixedIrregularCertificate67

end

end Fermat.SixtySeven.GenericProof
