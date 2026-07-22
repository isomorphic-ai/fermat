import Fermat.Basic
import Fermat.Classical
import Fermat.Eleven.Cyclotomic
import Fermat.Five.Dirichlet
import Fermat.Fourteen.DescentConstruction
import Fermat.Seven.Lebesgue.TheoremTwo
import Fermat.Thirteen.Cyclotomic

namespace Fermat

/-- Fermat's Last Theorem for exponent five, through Dirichlet's historical
two-branch descent. -/
theorem holdsAt_five : HoldsAt 5 := Five.Dirichlet.holdsAt_five_dirichlet

/-- Fermat's theorem for exponent seven, through Lebesgue's corrected 1840
proof (the main note together with its published Addition). -/
theorem holdsAt_seven : HoldsAt 7 := Seven.Lebesgue.holdsAt_seven_lebesgue

/-- Fermat's theorem for exponent fourteen, through Dirichlet's independent
1832 descent rather than the short consequence of exponent seven. -/
theorem holdsAt_fourteen : HoldsAt 14 :=
  Fourteen.Dirichlet.holdsAt_fourteen_dirichlet

/-- Fermat's theorem for exponent thirteen, via the class-number-one
certificate for `\mathbb{Q}(\zeta_{13})` and the formal Lamé–Kummer descent. -/
theorem holdsAt_thirteen : HoldsAt 13 :=
  Thirteen.Cyclotomic.holdsAt_thirteen_cyclotomic

/-- Fermat's theorem for exponent eleven, via the class-number-one
certificate for `\mathbb{Q}(\zeta_{11})` and the formal Lamé–Kummer descent. -/
theorem holdsAt_eleven : HoldsAt 11 :=
  Eleven.Cyclotomic.holdsAt_eleven_cyclotomic

end Fermat
