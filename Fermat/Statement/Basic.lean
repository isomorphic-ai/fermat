import Mathlib.NumberTheory.FLT.Basic

/-!
# The fixed-exponent Fermat proposition

This is the proposition-only boundary for conservation developments whose
import cone must not contain any exponent-transport theorem.  The repository
transport wrapper deliberately lives in the wider statement facade, not
here.
-/

namespace Fermat

/-- The project's short name for Mathlib's fixed-exponent FLT statement. -/
abbrev HoldsAt (n : ℕ) : Prop := FermatLastTheoremFor n

end Fermat
