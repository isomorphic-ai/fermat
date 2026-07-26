import Fermat.GenericIrregular.FixedExponent
import Fermat.SixHundredNinetyOne.FirstCase
import Fermat.SixHundredNinetyOne.GenericSecondCase

/-!
# FLT at exponent 691 through the generic fixed-exponent interface

The concrete plus-class, diagonal-unit, derivative, and two-channel axis-8
data are packaged as a `FixedIrregularCertificate`, the fixed-second-case
input to the prime-generic theorem.  That theorem combines it with the
generic proof-producing Sophie--Germain search to prove
`Fermat.HoldsAt 691`.  The explicit concrete Sophie--Germain certificate
below is a standalone finite regression; the endpoint does not consume it.
-/

open scoped NumberField

namespace Fermat.SixHundredNinetyOne.GenericProof

noncomputable section

open Fermat.GenericIrregular.FixedExponent

local instance : Fact (Nat.Prime 691) :=
  ⟨Fermat.SixHundredNinetyOne.prime_691⟩

/-- The finite Sophie--Germain residue certificate at auxiliary prime
`11057`. -/
def sophieGermainCertificate691 : SophieGermainCertificate 691 where
  auxiliaryPrime := 11057
  auxiliaryPrime_isPrime :=
    Fermat.SixHundredNinetyOne.prime_11057
  noConsecutivePowers :=
    Fermat.SixHundredNinetyOne.noConsecutivePowers_691_11057
  exponentNotPower :=
    Fermat.SixHundredNinetyOne.exponentNotPower_691_11057

/-- The fixed-second-case certificate at `691`.

Case I is supplied separately by the generic Sophie--Germain search. -/
def fixedIrregularCertificate691 :
    FixedIrregularCertificate 691 2 := by
  letI : NeZero (691 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {691} ℚ (CyclotomicField 691 ℚ) :=
    CyclotomicField.isCyclotomicExtension 691 ℚ
  have hroot :
      ∃ ζ : CyclotomicField 691 ℚ, IsPrimitiveRoot ζ 691 :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 691 ℚ)
      (Set.mem_singleton 691) (by norm_num : 691 ≠ 0)
  let ζ := Classical.choose hroot
  have hζ : IsPrimitiveRoot ζ 691 :=
    Classical.choose_spec hroot
  exact
    { exponent_atLeastFive := by norm_num
      secondCase :=
        Fermat.SixHundredNinetyOne.GenericSecondCase.fixedSecondCaseCertificate691
          hζ }

/-- Fermat's Last Theorem at exponent `691`, obtained solely through the
new prime-generic fixed-exponent theorem. -/
theorem holdsAt_sixHundredNinetyOne_generic : Fermat.HoldsAt 691 :=
  holdsAt_of_certificate fixedIrregularCertificate691

end

end Fermat.SixHundredNinetyOne.GenericProof
