import Fermat.Basic
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.FLT.Three

/-!
# Completed classical fixed-exponent cases

The complete `n = 3` and `n = 4` descent proofs are already part of mathlib.
This module exposes them through this project's common API.
-/

namespace Fermat

theorem holdsAt_three : HoldsAt 3 := fermatLastTheoremThree

theorem holdsAt_four : HoldsAt 4 := fermatLastTheoremFour

/-- The `n = 14` case follows formally from the `n = 7` case. -/
theorem holdsAt_fourteen_of_seven (hseven : HoldsAt 7) : HoldsAt 14 := by
  exact hseven.mono_of_dvd (by norm_num)

end Fermat
