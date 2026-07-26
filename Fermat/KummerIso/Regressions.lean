import Fermat.KummerIso.FixedExponent
import Fermat.ThirtySeven.GenericProof
import Fermat.FiftyNine.GenericProof
import Fermat.SixtySeven.GenericProof
import Fermat.OneHundredFiftySeven.GenericProof
import Fermat.FourHundredNinetyOne.GenericProof
import Fermat.FiveHundredEightySeven.GenericProof
import Fermat.SixHundredSeven.GenericProof
import Fermat.SixHundredNinetyOne.GenericProof
import Fermat.OneThousandThreeHundredEightyOne.GenericProof

/-!
# Fixed-exponent regressions through the Kummer correction

Each theorem in this file feeds an existing fixed-second-case
`GenericIrregular.FixedExponent.FixedIrregularCertificate` into the new
`KummerIso.FixedExponent` assembly.  Thus every regression traverses the
normalized correction automorphism and `KummerIso.UnitExtraction`, then
obtains Case I from the generic proof-producing Sophie--Germain search.

The existing `holdsAt_*_generic` conclusions and the standalone concrete
Sophie--Germain certificates are deliberately not used.
-/

namespace Fermat.KummerIso.Regressions

/-- FLT at exponent `37`, reassembled through the normalized Kummer
correction. -/
theorem holdsAt_thirtySeven : Fermat.HoldsAt 37 := by
  letI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  exact
    Fermat.KummerIso.FixedExponent.holdsAt_of_certificate
      Fermat.ThirtySeven.GenericProof.fixedIrregularCertificate37

/-- FLT at exponent `59`, reassembled through the normalized Kummer
correction. -/
theorem holdsAt_fiftyNine : Fermat.HoldsAt 59 := by
  letI : Fact (Nat.Prime 59) := ⟨by norm_num⟩
  exact
    Fermat.KummerIso.FixedExponent.holdsAt_of_certificate
      Fermat.FiftyNine.GenericProof.fixedIrregularCertificate59

/-- FLT at exponent `67`, reassembled through the normalized Kummer
correction. -/
theorem holdsAt_sixtySeven : Fermat.HoldsAt 67 := by
  letI : Fact (Nat.Prime 67) :=
    ⟨Fermat.SixtySeven.prime_67⟩
  exact
    Fermat.KummerIso.FixedExponent.holdsAt_of_certificate
      Fermat.SixtySeven.GenericProof.fixedIrregularCertificate67

/-- FLT at exponent `157`, reassembled through the normalized Kummer
correction. -/
theorem holdsAt_oneHundredFiftySeven : Fermat.HoldsAt 157 := by
  letI : Fact (Nat.Prime 157) :=
    ⟨Fermat.OneHundredFiftySeven.prime_157⟩
  exact
    Fermat.KummerIso.FixedExponent.holdsAt_of_certificate
      Fermat.OneHundredFiftySeven.GenericProof.fixedIrregularCertificate157

/-- FLT at exponent `491`, reassembled through the normalized Kummer
correction. -/
theorem holdsAt_fourHundredNinetyOne : Fermat.HoldsAt 491 := by
  letI : Fact (Nat.Prime 491) :=
    ⟨Fermat.FourHundredNinetyOne.prime_491⟩
  exact
    Fermat.KummerIso.FixedExponent.holdsAt_of_certificate
      Fermat.FourHundredNinetyOne.GenericProof.fixedIrregularCertificate491

/-- FLT at exponent `587`, reassembled through the normalized Kummer
correction. -/
theorem holdsAt_fiveHundredEightySeven : Fermat.HoldsAt 587 := by
  letI : Fact (Nat.Prime 587) :=
    ⟨Fermat.FiveHundredEightySeven.prime_587⟩
  exact
    Fermat.KummerIso.FixedExponent.holdsAt_of_certificate
      Fermat.FiveHundredEightySeven.GenericProof.fixedIrregularCertificate587

/-- FLT at exponent `607`, reassembled through the normalized Kummer
correction. -/
theorem holdsAt_sixHundredSeven : Fermat.HoldsAt 607 := by
  letI : Fact (Nat.Prime 607) :=
    ⟨Fermat.SixHundredSeven.prime_607⟩
  exact
    Fermat.KummerIso.FixedExponent.holdsAt_of_certificate
      Fermat.SixHundredSeven.GenericProof.fixedIrregularCertificate607

/-- FLT at exponent `691`, reassembled through the normalized Kummer
correction. -/
theorem holdsAt_sixHundredNinetyOne : Fermat.HoldsAt 691 := by
  letI : Fact (Nat.Prime 691) :=
    ⟨Fermat.SixHundredNinetyOne.prime_691⟩
  exact
    Fermat.KummerIso.FixedExponent.holdsAt_of_certificate
      Fermat.SixHundredNinetyOne.GenericProof.fixedIrregularCertificate691

/-- FLT at exponent `1381`, reassembled through the normalized Kummer
correction. -/
theorem holdsAt_oneThousandThreeHundredEightyOne :
    Fermat.HoldsAt 1381 := by
  letI : Fact (Nat.Prime 1381) :=
    ⟨Fermat.OneThousandThreeHundredEightyOne.prime_1381⟩
  exact
    Fermat.KummerIso.FixedExponent.holdsAt_of_certificate
      Fermat.OneThousandThreeHundredEightyOne.GenericProof.fixedIrregularCertificate1381

end Fermat.KummerIso.Regressions
