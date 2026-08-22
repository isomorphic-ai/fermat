import Fermat.Descent.GenericIrregular.FixedExponent
import Fermat.Exponents.OneThousandThreeHundredEightyOne.FirstCase
import Fermat.Exponents.OneThousandThreeHundredEightyOne.GenericSecondCase

/-!
# FLT at exponent 1381 through the generic fixed-exponent interface

This is the end-to-end regression.  The concrete plus-class, diagonal-unit,
derivative, and one-channel axis-8 data are packaged as a
`FixedIrregularCertificate`, the fixed-second-case input to the
prime-generic theorem.  That theorem combines it with the generic
proof-producing Sophie--Germain search to obtain `Fermat.HoldsAt 1381`.
The explicit concrete Sophie--Germain certificate below is a standalone
finite regression; the endpoint does not consume it.
-/

open scoped NumberField

namespace Fermat.OneThousandThreeHundredEightyOne.GenericProof

noncomputable section

open Fermat.GenericIrregular.FixedExponent

local instance : Fact (Nat.Prime 1381) :=
  ⟨Fermat.OneThousandThreeHundredEightyOne.prime_1381⟩

/-- The finite Sophie--Germain residue certificate at auxiliary prime
38669. -/
def sophieGermainCertificate1381 : SophieGermainCertificate 1381 where
  auxiliaryPrime := 38669
  auxiliaryPrime_isPrime :=
    Fermat.OneThousandThreeHundredEightyOne.prime_38669
  noConsecutivePowers :=
    Fermat.OneThousandThreeHundredEightyOne.noConsecutivePowers_1381_38669
  exponentNotPower :=
    Fermat.OneThousandThreeHundredEightyOne.exponentNotPower_1381_38669

/-- The fixed-second-case certificate at `1381`.

A primitive root is chosen only to extract the root-independent plus-class
number statement from the concrete Sinnott--Kummer theorem.  Every unit and
derivative field remains uniform in the root later chosen by the generic
assembly.  Case I is supplied separately by the generic search. -/
def fixedIrregularCertificate1381 :
    FixedIrregularCertificate 1381 1 := by
  letI : NeZero (1381 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {1381} ℚ (CyclotomicField 1381 ℚ) :=
    CyclotomicField.isCyclotomicExtension 1381 ℚ
  have hroot :
      ∃ ζ : CyclotomicField 1381 ℚ, IsPrimitiveRoot ζ 1381 :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 1381 ℚ)
      (Set.mem_singleton 1381) (by norm_num : 1381 ≠ 0)
  let ζ := Classical.choose hroot
  have hζ : IsPrimitiveRoot ζ 1381 :=
    Classical.choose_spec hroot
  exact
    { exponent_atLeastFive := by norm_num
      secondCase :=
        Fermat.OneThousandThreeHundredEightyOne.GenericSecondCase.fixedSecondCaseCertificate1381
          hζ }

/-- Fermat's Last Theorem at exponent `1381`, obtained solely through the
prime-generic fixed-exponent theorem. -/
theorem holdsAt_oneThousandThreeHundredEightyOne_generic :
    Fermat.HoldsAt 1381 :=
  holdsAt_of_certificate fixedIrregularCertificate1381

end

end Fermat.OneThousandThreeHundredEightyOne.GenericProof
