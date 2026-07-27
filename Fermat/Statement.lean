import Mathlib.NumberTheory.FLT.Basic

/-!
# Fixed-exponent Fermat statements

This minimal module owns the project's common fixed-exponent statement. It
imports only Mathlib's definition-and-reduction module, so proofs that must
not see any already-completed fixed-exponent case can depend on this boundary
directly.
-/

namespace Fermat

/-- The project's short name for Mathlib's fixed-exponent FLT statement. -/
abbrev HoldsAt (n : ℕ) : Prop := FermatLastTheoremFor n

/-- A proved exponent transports to every multiple of that exponent. -/
theorem HoldsAt.mono_of_dvd {m n : ℕ}
    (hm : HoldsAt m) (hdiv : m ∣ n) :
    HoldsAt n := by
  exact FermatLastTheoremFor.mono hdiv hm

end Fermat
