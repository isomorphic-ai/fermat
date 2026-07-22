import Fermat.Basic
import Fermat.Eleven.PackageCertificate
import FltRegular.FltRegular

/-!
# Fermat's Last Theorem for exponent eleven

This file connects the uploaded class-number certificate for
`\mathbb{Q}(\zeta_{11})` to the fully formal Lamé–Kummer descent supplied by
`flt-regular`.
-/

namespace Fermat.Eleven.Cyclotomic

open Nat NumberField RingOfIntegers IsCyclotomicExtension

/-- The ring of integers in an eleventh cyclotomic field is a principal
ideal ring.  The proof uses the exact Minkowski bound and the norm-23
generator from the uploaded proof package. -/
theorem ringOfIntegers_isPrincipalIdealRing
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {11} ℚ K] :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K) :=
  PackageCertificate.ringOfIntegers_isPrincipalIdealRing K

set_option backward.isDefEq.respectTransparency false in
/-- Eleven is regular because its cyclotomic field has class number one. -/
theorem isRegularPrime_eleven :
    haveI : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
    IsRegularPrime 11 := by
  rw [IsRegularPrime, IsRegularNumber]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2
    (ringOfIntegers_isPrincipalIdealRing (CyclotomicField 11 ℚ))

/-- Fermat's Last Theorem for exponent eleven, obtained by feeding the
class-number-one certificate into the formal Lamé–Kummer theorem. -/
theorem holdsAt_eleven_cyclotomic : Fermat.HoldsAt 11 := by
  exact @flt_regular 11 ⟨Nat.prime_eleven⟩ isRegularPrime_eleven (by omega)

end Fermat.Eleven.Cyclotomic
