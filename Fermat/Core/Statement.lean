import Fermat.Core.Statement.Basic

/-!
# Fixed-exponent Fermat statements

This facade owns the project's common fixed-exponent statement together with
the standard divisibility transport.  Conservation proofs whose import cone
must not expose that transport should import `Fermat.Statement.Basic`
instead.
-/

namespace Fermat

/-- A proved exponent transports to every multiple of that exponent. -/
theorem HoldsAt.mono_of_dvd {m n : ℕ}
    (hm : HoldsAt m) (hdiv : m ∣ n) :
    HoldsAt n := by
  exact FermatLastTheoremFor.mono hdiv hm

end Fermat
