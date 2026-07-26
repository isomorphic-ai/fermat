import Fermat.KummerIso.WeightedSolution
import Fermat.KummerIso.Principalization
import Fermat.KummerIso.Correction
import Fermat.KummerIso.UnitExtraction
import Fermat.KummerIso.DeepRatio
import Fermat.KummerIso.Induction
import Fermat.KummerIso.SecondCase
import Fermat.KummerIso.ValidatedSecondCase
import Fermat.KummerIso.FermatEquationSevenDBruteForce
import Fermat.KummerIso.FixedExponent
import Fermat.KummerIso.Regressions

/-!
# The regularized Kummer splice

This is the umbrella import for the irregular-prime Kummer repair.

The stack separates the two places where the regular-prime proof uses
regularity:

* `Principalization` repairs the special Fermat ideal roots through the
  historical primary/Takagi--Furtwängler route;
* `Correction` and `UnitExtraction` repair the unit step by an invertible
  diagonal normalization of the lifted Bernoulli coefficients.

`SecondCase` and `FixedExponent` assemble the complete historical route.
`ValidatedSecondCase` exposes the prime-generic Case-II endpoint through
the two deliberately named temporary validation seams.
`FermatEquationSevenDBruteForce` removes the equation-(7d) seam for any
fixed prime carrying a kernel-checked circular-unit residue certificate.
`Induction` records the conditional regular-style adapter: once the
displayed unit-ratio depth premise is supplied, it absorbs the resulting
`p`-th root and removes the left-hand weights from the equation.
`Regressions` checks the common construction at the nine completed
fixed exponents from `37` through `1381`.

See `Fermat/KummerIso/README.md` for the dependency map and the exact
remaining boundary for direct reuse of the regular-style weighted witness.
-/
