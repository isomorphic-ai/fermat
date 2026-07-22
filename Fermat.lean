import Fermat.Basic
import Fermat.Classical
import Fermat.Five.Dirichlet
import Fermat.Fourteen.DescentConstruction

namespace Fermat

/-- Fermat's Last Theorem for exponent five, through Dirichlet's historical
two-branch descent. -/
theorem holdsAt_five : HoldsAt 5 := Five.Dirichlet.holdsAt_five_dirichlet

end Fermat
