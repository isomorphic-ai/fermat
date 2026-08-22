import Fermat.Core.Basic
import Fermat.Descent.Regular.KummerCriterion
import Fermat.Exponents.Thirteen.PackageCertificate

/-!
# Fermat's Last Theorem for exponent thirteen

This file records the finite class-number calculation for
`\mathbb{Q}(\zeta_{13})` against the project's explicit historical
class-number predicate.  It also exposes the fixed-exponent FLT endpoint
from the patched generic `flt-regular` descent.

The patched descent no longer consumes class-number regularity, so these are
two independently checked results rather than a premise and its consumer.
-/

namespace Fermat.Thirteen.Cyclotomic

open Nat NumberField RingOfIntegers IsCyclotomicExtension
open Fermat.Regular.Faulhaber

/-- The ring of integers in a thirteenth cyclotomic field is a principal
ideal ring.  The proof uses the exact Minkowski bound and the five
prime-ideal generators from the uploaded proof package. -/
theorem ringOfIntegers_isPrincipalIdealRing
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {13} ℚ K] :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K) :=
  PackageCertificate.ringOfIntegers_isPrincipalIdealRing K

set_option backward.isDefEq.respectTransparency false in
/-- Thirteen satisfies the historical cyclotomic class-number condition
because its cyclotomic field has class number one. -/
theorem cyclotomicClassNumberRegular_thirteen :
    CyclotomicClassNumberRegular 13 := by
  rw [CyclotomicClassNumberRegular]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2
    (ringOfIntegers_isPrincipalIdealRing (CyclotomicField 13 ℚ))

/-- Fermat's Last Theorem for exponent thirteen from the patched generic
descent.  Unlike the class-number theorem above, this inherits the generic
core's temporary project seams. -/
theorem holdsAt_thirteen_cyclotomic : Fermat.HoldsAt 13 := by
  exact @flt_regular 13 ⟨Nat.prime_thirteen⟩ (by omega)

end Fermat.Thirteen.Cyclotomic
