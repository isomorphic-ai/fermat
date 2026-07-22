import Fermat.Basic
import FltRegular.SmallNumbers.Thirteen.FLT13

/-!
# Fermat's Last Theorem for exponent thirteen

This file connects the finite class-number calculation for
`\mathbb{Q}(\zeta_{13})` to the fully formal Lamé–Kummer descent supplied by
`flt-regular`.
-/

namespace Fermat.Thirteen.Cyclotomic

open Nat NumberField RingOfIntegers IsCyclotomicExtension

/-- The ring of integers in a thirteenth cyclotomic field is a principal
ideal ring.  The proof uses the exact Minkowski bound and finite prime-ideal
certificates in `FltRegular.SmallNumbers.Thirteen.Thirteen`. -/
theorem ringOfIntegers_isPrincipalIdealRing
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {13} ℚ K] :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K) :=
  Rat.thirteen_pid K

/-- Thirteen is regular because its cyclotomic field has class number one. -/
theorem isRegularPrime_thirteen : IsRegularPrime 13 := by
  simpa using _root_.isRegularPrime_thirteen

/-- Fermat's Last Theorem for exponent thirteen, obtained by feeding the
class-number-one certificate into the formal Lamé–Kummer theorem. -/
theorem holdsAt_thirteen_cyclotomic : Fermat.HoldsAt 13 := by
  exact @flt_regular 13 ⟨Nat.prime_thirteen⟩ isRegularPrime_thirteen (by omega)

end Fermat.Thirteen.Cyclotomic
