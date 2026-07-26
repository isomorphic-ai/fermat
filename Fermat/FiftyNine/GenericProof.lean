import Fermat.GenericIrregular.FixedExponent
import Fermat.FiftyNine.FirstCase
import Fermat.FiftyNine.GenericSecondCase

/-!
# FLT at exponent 59 through the generic fixed-exponent interface

This file is the end-to-end regression: the concrete plus-class,
diagonal-unit, derivative, and axis-8 channel data are packaged as a
`FixedIrregularCertificate`, the fixed-second-case input to the
prime-generic theorem.  That theorem combines it with the generic
proof-producing Sophie--Germain search to obtain `Fermat.HoldsAt 59`.
The explicit concrete Sophie--Germain certificate below is an independent
finite-check regression; the endpoint does not consume it.
-/

open scoped NumberField

namespace Fermat.FiftyNine.GenericProof

noncomputable section

open Fermat.GenericIrregular.FixedExponent

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

/-- The finite Sophie--Germain residue certificate at auxiliary prime 827. -/
def sophieGermainCertificate59 : SophieGermainCertificate 59 where
  auxiliaryPrime := 827
  auxiliaryPrime_isPrime :=
    Fermat.FiftyNine.prime_827
  noConsecutivePowers :=
    Fermat.FiftyNine.noConsecutivePowers_59_827
  exponentNotPower :=
    Fermat.FiftyNine.exponentNotPower_59_827

/-- The fixed-second-case certificate at `59`.

A primitive root is chosen only to extract the root-independent
plus-class-number statement from the concrete Sinnott--Kummer theorem.
Every unit and derivative field remains uniform in the later root chosen
by the generic assembly.  Case I is supplied separately by the generic
search. -/
def fixedIrregularCertificate59 :
    FixedIrregularCertificate 59 1 := by
  letI : NeZero (59 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {59} ℚ (CyclotomicField 59 ℚ) :=
    CyclotomicField.isCyclotomicExtension 59 ℚ
  have hroot :
      ∃ ζ : CyclotomicField 59 ℚ, IsPrimitiveRoot ζ 59 :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 59 ℚ)
      (Set.mem_singleton 59) (by norm_num : 59 ≠ 0)
  let ζ := Classical.choose hroot
  have hζ : IsPrimitiveRoot ζ 59 :=
    Classical.choose_spec hroot
  exact
    { exponent_atLeastFive := by norm_num
      secondCase :=
        Fermat.FiftyNine.GenericSecondCase.fixedSecondCaseCertificate59
          hζ }

/-- Fermat's Last Theorem at exponent `59`, obtained solely through the
new prime-generic fixed-exponent theorem. -/
theorem holdsAt_fiftyNine_generic : Fermat.HoldsAt 59 :=
  holdsAt_of_certificate fixedIrregularCertificate59

end

end Fermat.FiftyNine.GenericProof
