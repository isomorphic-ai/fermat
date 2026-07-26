import Fermat.GenericIrregular.FixedExponent
import Fermat.FiveHundredEightySeven.FirstCase
import Fermat.FiveHundredEightySeven.GenericSecondCase

/-!
# FLT at exponent 587 through the generic fixed-exponent interface

This is the end-to-end regression.  The concrete plus-class, diagonal-unit,
derivative, and two-channel axis-8 data are packaged as a
`FixedIrregularCertificate`, the fixed-second-case input to the
prime-generic theorem.  That theorem combines it with the generic
proof-producing Sophie--Germain search to obtain `Fermat.HoldsAt 587`.
The explicit concrete Sophie--Germain certificate below is a standalone
finite regression; the endpoint does not consume it.
-/

open scoped NumberField

namespace Fermat.FiveHundredEightySeven.GenericProof

noncomputable section

open Fermat.GenericIrregular.FixedExponent

local instance : Fact (Nat.Prime 587) :=
  ⟨Fermat.FiveHundredEightySeven.prime_587⟩

/-- The finite Sophie--Germain residue certificate at auxiliary prime 8219. -/
def sophieGermainCertificate587 : SophieGermainCertificate 587 where
  auxiliaryPrime := 8219
  auxiliaryPrime_isPrime :=
    Fermat.FiveHundredEightySeven.prime_8219
  noConsecutivePowers :=
    Fermat.FiveHundredEightySeven.noConsecutivePowers_587_8219
  exponentNotPower :=
    Fermat.FiveHundredEightySeven.exponentNotPower_587_8219

/-- The fixed-second-case certificate at `587`.

A primitive root is chosen only to extract the root-independent plus-class
number statement from the concrete Sinnott--Kummer theorem.  Every unit and
derivative field remains uniform in the root later chosen by the generic
assembly.  Case I is supplied separately by the generic search. -/
def fixedIrregularCertificate587 :
    FixedIrregularCertificate 587 2 := by
  letI : NeZero (587 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {587} ℚ (CyclotomicField 587 ℚ) :=
    CyclotomicField.isCyclotomicExtension 587 ℚ
  have hroot :
      ∃ ζ : CyclotomicField 587 ℚ, IsPrimitiveRoot ζ 587 :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 587 ℚ)
      (Set.mem_singleton 587) (by norm_num : 587 ≠ 0)
  let ζ := Classical.choose hroot
  have hζ : IsPrimitiveRoot ζ 587 :=
    Classical.choose_spec hroot
  exact
    { exponent_atLeastFive := by norm_num
      secondCase :=
        Fermat.FiveHundredEightySeven.GenericSecondCase.fixedSecondCaseCertificate587
          hζ }

/-- Fermat's Last Theorem at exponent `587`, obtained solely through the
prime-generic fixed-exponent theorem. -/
theorem holdsAt_fiveHundredEightySeven_generic : Fermat.HoldsAt 587 :=
  holdsAt_of_certificate fixedIrregularCertificate587

end

end Fermat.FiveHundredEightySeven.GenericProof
