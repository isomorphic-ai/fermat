import Fermat.Core.Basic
import Fermat.Exponents.Eleven.PackageCertificate
import Fermat.Descent.Regular.KummerCriterion

/-!
# Fermat's Last Theorem for exponent eleven

This file records the uploaded class-number certificate for
`\mathbb{Q}(\zeta_{11})` against the project's explicit historical
class-number predicate.  It also exposes the fixed-exponent FLT endpoint
from the patched generic `flt-regular` descent.

The patched descent no longer consumes class-number regularity, so these are
two independently checked results rather than a premise and its consumer.
-/

namespace Fermat.Eleven.Cyclotomic

open Nat NumberField RingOfIntegers IsCyclotomicExtension
open Fermat.Regular.Faulhaber

/-- The ring of integers in an eleventh cyclotomic field is a principal
ideal ring.  The proof uses the exact Minkowski bound and the norm-23
generator from the uploaded proof package. -/
theorem ringOfIntegers_isPrincipalIdealRing
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {11} ℚ K] :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K) :=
  PackageCertificate.ringOfIntegers_isPrincipalIdealRing K

set_option backward.isDefEq.respectTransparency false in
/-- Eleven satisfies the historical cyclotomic class-number condition
because its cyclotomic field has class number one. -/
theorem cyclotomicClassNumberRegular_eleven :
    CyclotomicClassNumberRegular 11 := by
  rw [CyclotomicClassNumberRegular]
  convert coprime_one_right _
  exact classNumber_eq_one_iff.2
    (ringOfIntegers_isPrincipalIdealRing (CyclotomicField 11 ℚ))

/-- Fermat's Last Theorem for exponent eleven from the patched generic
descent.  Unlike the class-number theorem above, this inherits the generic
core's temporary project seams. -/
theorem holdsAt_eleven_cyclotomic : Fermat.HoldsAt 11 := by
  exact @flt_regular 11 ⟨Nat.prime_eleven⟩ (by omega)

end Fermat.Eleven.Cyclotomic
