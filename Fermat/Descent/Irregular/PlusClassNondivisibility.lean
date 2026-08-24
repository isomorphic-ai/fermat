import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.CMField

/-!
# Plus-class-number nondivisibility

This lightweight module names the plus-class input used throughout the
irregular descent.  Keeping the proposition separate from the historical
implementation lets intrinsic channel certificates state their result
without importing any exponent-specific circular-unit receipt.
-/

open scoped NumberField

namespace Fermat.Irregular.VandiverHistoricalPrime

/-- The exact plus-class input used in Vandiver's real-ideal steps. -/
def PlusClassNondivisibility (K : Type*) [Field K] [NumberField K]
    (p : ℕ) : Prop :=
  ¬ p ∣ NumberField.classNumber (NumberField.maximalRealSubfield K)

end Fermat.Irregular.VandiverHistoricalPrime
