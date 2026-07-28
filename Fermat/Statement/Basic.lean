import Mathlib.NumberTheory.FLT.Basic

/-!
# The fixed-exponent Fermat proposition

This is the proposition-only boundary for conservation developments whose
import cone must not contain any exponent-transport theorem.  In particular,
`Fermat.HoldsAt.mono_of_dvd` deliberately lives in the wider
`Fermat.Statement` facade, not here.
-/

namespace Fermat

/-- The project's short name for Mathlib's fixed-exponent FLT statement. -/
abbrev HoldsAt (n : ℕ) : Prop := FermatLastTheoremFor n

end Fermat
