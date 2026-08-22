import Fermat.Descent.GenericIrregular.FixedExponent
import Fermat.Exponents.SixHundredSeven.FirstCase
import Fermat.Exponents.SixHundredSeven.GenericSecondCase

/-!
# FLT at exponent 607 through the generic fixed-exponent interface

The concrete plus-class, diagonal-unit, derivative, and one-channel axis-8
data are packaged as a `FixedIrregularCertificate`, the fixed-second-case
input to the prime-generic theorem.  That theorem combines it with the
generic proof-producing Sophie--Germain search to prove
`Fermat.HoldsAt 607`.  The explicit concrete Sophie--Germain certificate
below is a standalone finite regression; the endpoint does not consume it.
-/

open scoped NumberField

namespace Fermat.SixHundredSeven.GenericProof

noncomputable section

open Fermat.GenericIrregular.FixedExponent

local instance : Fact (Nat.Prime 607) :=
  ⟨Fermat.SixHundredSeven.prime_607⟩

/-- The finite Sophie--Germain residue certificate at auxiliary prime
`20639`. -/
def sophieGermainCertificate607 : SophieGermainCertificate 607 where
  auxiliaryPrime := 20639
  auxiliaryPrime_isPrime :=
    Fermat.SixHundredSeven.prime_20639
  noConsecutivePowers :=
    Fermat.SixHundredSeven.noConsecutivePowers_607_20639
  exponentNotPower :=
    Fermat.SixHundredSeven.exponentNotPower_607_20639

/-- The fixed-second-case certificate at `607`.

Case I is supplied separately by the generic Sophie--Germain search. -/
def fixedIrregularCertificate607 :
    FixedIrregularCertificate 607 1 := by
  letI : NeZero (607 : ℚ) := ⟨by norm_num⟩
  letI :
      IsCyclotomicExtension {607} ℚ (CyclotomicField 607 ℚ) :=
    CyclotomicField.isCyclotomicExtension 607 ℚ
  have hroot :
      ∃ ζ : CyclotomicField 607 ℚ, IsPrimitiveRoot ζ 607 :=
    IsCyclotomicExtension.exists_isPrimitiveRoot
      ℚ (CyclotomicField 607 ℚ)
      (Set.mem_singleton 607) (by norm_num : 607 ≠ 0)
  let ζ := Classical.choose hroot
  have hζ : IsPrimitiveRoot ζ 607 :=
    Classical.choose_spec hroot
  exact
    { exponent_atLeastFive := by norm_num
      secondCase :=
        Fermat.SixHundredSeven.GenericSecondCase.fixedSecondCaseCertificate607
          hζ }

/-- Fermat's Last Theorem at exponent `607`, obtained solely through the
prime-generic fixed-exponent theorem. -/
theorem holdsAt_sixHundredSeven_generic : Fermat.HoldsAt 607 :=
  holdsAt_of_certificate fixedIrregularCertificate607

end

end Fermat.SixHundredSeven.GenericProof
