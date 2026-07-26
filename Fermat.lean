import Fermat.Basic
import Fermat.Cases
import Fermat.Classical
import Fermat.Eleven.Cyclotomic
import Fermat.Eleven.SevenFold
import Fermat.FiftyNine.GenericProof
import Fermat.Five.Dirichlet
import Fermat.FiveHundredEightySeven.GenericProof
import Fermat.Fourteen.DescentConstruction
import Fermat.FourHundredNinetyOne.GenericProof
import Fermat.FourHundredNinetyOne.SecondCase
import Fermat.GenericIrregular
import Fermat.KummerIso
import Fermat.Irregular.CircularUnitIndex
import Fermat.Irregular.CircularUnits
import Fermat.Irregular.CyclotomicLogCofactor37
import Fermat.Irregular.CyclotomicDirichlet37
import Fermat.Irregular.CyclotomicLValue37
import Fermat.Irregular.CyclotomicSeriesAtOne37
import Fermat.Irregular.KummerCongruence
import Fermat.Irregular.VandiverData
import Fermat.Ladder.FaulhaberResponse
import Fermat.Ladder.HistoricalResponse
import Fermat.Ladder.Response
import Fermat.OneHundredFiftySeven.GenericProof
import Fermat.OneThousandFiftyOne.Regularity
import Fermat.OneThousandThreeHundredEightyOne.GenericProof
import Fermat.OneThousandThreeHundredEightyOne.VandiverHistoricalAssembly1381
import Fermat.Seven.Lebesgue.TheoremTwo
import Fermat.SixHundredNinetyOne.GenericProof
import Fermat.SixHundredSeven.VandiverHistoricalAssembly607
import Fermat.SixHundredSeven.GenericProof
import Fermat.SixHundredNinetyOne.SecondCase
import Fermat.SixtySeven.GenericProof
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
import Fermat.ThirtySeven.GenericProof
import Fermat.TwoHundredTwentyNine.Regularity

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
quadratic fold and direct Faulhaber proof through Kummer's criterion. -/
theorem holdsAt_thirteen_sevenFold : HoldsAt 13 :=
  Thirteen.SevenFold.holdsAt_thirteen_sevenFold

/-- Fermat's theorem for exponent thirteen from the five direct Faulhaber
power-sum certificates, Kummer's criterion, and `flt_regular`. -/
theorem holdsAt_thirteen_faulhaber : HoldsAt 13 :=
  Thirteen.SevenFold.holdsAt_thirteen_faulhaber

/-- Fermat's theorem for exponent eleven, via the class-number-one
certificate for `\mathbb{Q}(\zeta_{11})` and the formal Lamé–Kummer descent. -/
theorem holdsAt_eleven : HoldsAt 11 :=
  Eleven.Cyclotomic.holdsAt_eleven_cyclotomic

/-- The same exponent-eleven endpoint packaged with its decompressed
quadratic fold and direct Faulhaber proof through Kummer's criterion. -/
theorem holdsAt_eleven_sevenFold : HoldsAt 11 :=
  Eleven.SevenFold.holdsAt_eleven_sevenFold

/-- Fermat's theorem for exponent eleven from the four direct Faulhaber
power-sum certificates, Kummer's criterion, and `flt_regular`. -/
theorem holdsAt_eleven_faulhaber : HoldsAt 11 :=
  Eleven.SevenFold.holdsAt_eleven_faulhaber

/-- Fermat's theorem for exponent thirty-seven, through the complete
historical Vandiver assembly reused by the seven-fold ladder. -/
theorem holdsAt_thirtySeven : HoldsAt 37 :=
  ThirtySeven.holdsAt_thirtySeven

/-- The same exponent through the parameterized fixed-irregular
certificate theorem. -/
theorem holdsAt_thirtySeven_generic : HoldsAt 37 :=
  ThirtySeven.GenericProof.holdsAt_thirtySeven_generic

/-- Fermat's theorem for exponent fifty-nine, through the complete
historical Vandiver assembly reused by the seven-fold ladder. -/
theorem holdsAt_fiftyNine : HoldsAt 59 :=
  FiftyNine.holdsAt_fiftyNine

/-- The same exponent through the parameterized fixed-irregular
certificate theorem. -/
theorem holdsAt_fiftyNine_generic : HoldsAt 59 :=
  FiftyNine.GenericProof.holdsAt_fiftyNine_generic

/-- Fermat's theorem for exponent sixty-seven, through the complete
historical Vandiver assembly reused by the seven-fold ladder. -/
theorem holdsAt_sixtySeven : HoldsAt 67 :=
  SixtySeven.holdsAt_sixtySeven

/-- The same exponent through the parameterized fixed-irregular
certificate theorem. -/
theorem holdsAt_sixtySeven_generic : HoldsAt 67 :=
  SixtySeven.GenericProof.holdsAt_sixtySeven_generic

/-- Fermat's theorem for exponent one hundred fifty-seven, including the
two-probe finite loop and historical Vandiver descent reused by the ladder. -/
theorem holdsAt_oneHundredFiftySeven : HoldsAt 157 :=
  OneHundredFiftySeven.holdsAt_oneHundredFiftySeven

/-- The same exponent through the parameterized fixed-irregular
certificate theorem. -/
theorem holdsAt_oneHundredFiftySeven_generic : HoldsAt 157 :=
  OneHundredFiftySeven.GenericProof.holdsAt_oneHundredFiftySeven_generic

/-- Fermat's theorem for exponent two hundred twenty-nine, from a complete
depth-one Voronoi scan, Kummer's regular-prime criterion, and the formal
Lamé--Kummer descent. -/
theorem holdsAt_twoHundredTwentyNine : HoldsAt 229 :=
  TwoHundredTwentyNine.holdsAt_twoHundredTwentyNine

/-- Fermat's theorem for exponent four hundred ninety-one, through the
three-channel Vandiver--Takagi--Furtwängler assembly reused by the
seven-fold ladder. -/
theorem holdsAt_fourHundredNinetyOne : HoldsAt 491 :=
  FourHundredNinetyOne.holdsAt_fourHundredNinetyOne

/-- The same exponent through the parameterized fixed-irregular
certificate theorem. -/
theorem holdsAt_fourHundredNinetyOne_generic : HoldsAt 491 :=
  FourHundredNinetyOne.GenericProof.holdsAt_fourHundredNinetyOne_generic

/-- Fermat's theorem for exponent five hundred eighty-seven, through the
two-channel historical Vandiver assembly reused by the seven-fold ladder. -/
theorem holdsAt_fiveHundredEightySeven : HoldsAt 587 :=
  FiveHundredEightySeven.holdsAt_fiveHundredEightySeven

/-- The same exponent through the parameterized fixed-irregular
certificate theorem. -/
theorem holdsAt_fiveHundredEightySeven_generic : HoldsAt 587 :=
  FiveHundredEightySeven.GenericProof.holdsAt_fiveHundredEightySeven_generic

/-- Fermat's theorem for exponent six hundred seven, through the
one-channel circular-unit certificate, Vandiver's Lemma II, and the
historical descent. -/
theorem holdsAt_sixHundredSeven : HoldsAt 607 :=
  SixHundredSeven.holdsAt_sixHundredSeven

/-- The same exponent through the parameterized fixed-irregular
certificate theorem. -/
theorem holdsAt_sixHundredSeven_generic : HoldsAt 607 :=
  SixHundredSeven.GenericProof.holdsAt_sixHundredSeven_generic

/-- Fermat's theorem for exponent six hundred ninety-one, through the
two-channel Vandiver--Takagi--Furtwängler assembly reused by the
seven-fold ladder. -/
theorem holdsAt_sixHundredNinetyOne : HoldsAt 691 :=
  SixHundredNinetyOne.holdsAt_sixHundredNinetyOne

/-- The same exponent through the parameterized fixed-irregular
certificate theorem. -/
theorem holdsAt_sixHundredNinetyOne_generic : HoldsAt 691 :=
  SixHundredNinetyOne.GenericProof.holdsAt_sixHundredNinetyOne_generic

/-- Fermat's theorem for exponent one thousand fifty-one, from a complete
Bernoulli regularity scan and the formal Lamé--Kummer descent. -/
theorem holdsAt_oneThousandFiftyOne : HoldsAt 1051 :=
  OneThousandFiftyOne.holdsAt_oneThousandFiftyOne

/-- Fermat's theorem for exponent one thousand three hundred eighty-one,
through the checked circular-unit certificate and the prime-generic
Vandiver--Takagi--Furtwängler historical assembly. -/
theorem holdsAt_oneThousandThreeHundredEightyOne : HoldsAt 1381 :=
  OneThousandThreeHundredEightyOne.holdsAt_oneThousandThreeHundredEightyOne

/-- The same exponent through the parameterized fixed-irregular
certificate theorem. -/
theorem holdsAt_oneThousandThreeHundredEightyOne_generic : HoldsAt 1381 :=
  OneThousandThreeHundredEightyOne.GenericProof.holdsAt_oneThousandThreeHundredEightyOne_generic

/-! ## Fixed-irregular regressions through the normalized Kummer correction -/

/-- Exponent `37`, reassembled through the regularized Kummer splice. -/
theorem holdsAt_thirtySeven_kummerIso : HoldsAt 37 :=
  KummerIso.Regressions.holdsAt_thirtySeven

/-- Exponent `59`, reassembled through the regularized Kummer splice. -/
theorem holdsAt_fiftyNine_kummerIso : HoldsAt 59 :=
  KummerIso.Regressions.holdsAt_fiftyNine

/-- Exponent `67`, reassembled through the regularized Kummer splice. -/
theorem holdsAt_sixtySeven_kummerIso : HoldsAt 67 :=
  KummerIso.Regressions.holdsAt_sixtySeven

/-- Exponent `157`, reassembled through the regularized Kummer splice. -/
theorem holdsAt_oneHundredFiftySeven_kummerIso : HoldsAt 157 :=
  KummerIso.Regressions.holdsAt_oneHundredFiftySeven

/-- Exponent `491`, reassembled through the regularized Kummer splice. -/
theorem holdsAt_fourHundredNinetyOne_kummerIso : HoldsAt 491 :=
  KummerIso.Regressions.holdsAt_fourHundredNinetyOne

/-- Exponent `587`, reassembled through the regularized Kummer splice. -/
theorem holdsAt_fiveHundredEightySeven_kummerIso : HoldsAt 587 :=
  KummerIso.Regressions.holdsAt_fiveHundredEightySeven

/-- Exponent `607`, reassembled through the regularized Kummer splice. -/
theorem holdsAt_sixHundredSeven_kummerIso : HoldsAt 607 :=
  KummerIso.Regressions.holdsAt_sixHundredSeven

/-- Exponent `691`, reassembled through the regularized Kummer splice. -/
theorem holdsAt_sixHundredNinetyOne_kummerIso : HoldsAt 691 :=
  KummerIso.Regressions.holdsAt_sixHundredNinetyOne

/-- Exponent `1381`, reassembled through the regularized Kummer splice. -/
theorem holdsAt_oneThousandThreeHundredEightyOne_kummerIso : HoldsAt 1381 :=
  KummerIso.Regressions.holdsAt_oneThousandThreeHundredEightyOne

end Fermat
