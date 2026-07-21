import Mathlib

/-!
# Fixed-exponent cases of Fermat's Last Theorem

This file fixes the common statement used by the classical proofs.  We use
mathlib's standard statement over the naturals; mathlib also proves it
equivalent to the corresponding statement over the integers and rationals.
-/

namespace Fermat

/-- The project's short name for mathlib's fixed-exponent FLT statement. -/
abbrev HoldsAt (n : ℕ) : Prop := FermatLastTheoremFor n

theorem HoldsAt.mono_of_dvd {m n : ℕ} (hm : HoldsAt m) (hdiv : m ∣ n) : HoldsAt n := by
  exact FermatLastTheoremFor.mono hdiv hm

end Fermat
