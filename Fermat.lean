import Fermat.Basic
import Fermat.Cases
import Fermat.Classical
import Fermat.Eleven.Cyclotomic
import Fermat.Eleven.SevenFold
import Fermat.Five.Dirichlet
import Fermat.Fourteen.DescentConstruction
import Fermat.Irregular.CircularUnitIndex
import Fermat.Irregular.CircularUnits
import Fermat.Irregular.CyclotomicLogCofactor37
import Fermat.Irregular.CyclotomicDirichlet37
import Fermat.Irregular.KummerCongruence
import Fermat.Irregular.VandiverData
import Fermat.Ladder.Response
import Fermat.Seven.Lebesgue.TheoremTwo
import Fermat.Thirteen.Cyclotomic
import Fermat.Thirteen.SevenFold
import Fermat.ThirtySeven.ArithmeticCertificate
import Fermat.ThirtySeven.CircularUnitCertificate
import Fermat.ThirtySeven.CircularUnitResidues
import Fermat.ThirtySeven.DirectVandiverData
import Fermat.ThirtySeven.FirstCase
import Fermat.ThirtySeven.HighBernoulli
import Fermat.ThirtySeven.NeighborFolding
import Fermat.ThirtySeven.ResidueHomomorphisms
import Fermat.ThirtySeven.VandiverData

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

/-- The same exponent-thirteen endpoint packaged with its decompressed
quadratic-fold and direct Faulhaber certificates. -/
theorem holdsAt_thirteen_sevenFold : HoldsAt 13 :=
  Thirteen.SevenFold.holdsAt_thirteen_sevenFold

/-- Fermat's theorem for exponent eleven, via the class-number-one
certificate for `\mathbb{Q}(\zeta_{11})` and the formal Lamé–Kummer descent. -/
theorem holdsAt_eleven : HoldsAt 11 :=
  Eleven.Cyclotomic.holdsAt_eleven_cyclotomic

/-- The same exponent-eleven endpoint packaged with its decompressed
quadratic-fold and direct Faulhaber certificates. -/
theorem holdsAt_eleven_sevenFold : HoldsAt 11 :=
  Eleven.SevenFold.holdsAt_eleven_sevenFold

end Fermat
