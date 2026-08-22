import Fermat.Descent.KummerIso.WeightedSolution
import Fermat.Descent.KummerIso.Principalization
import Fermat.Descent.KummerIso.Correction
import Fermat.Descent.KummerIso.UnitExtraction
import Fermat.Descent.KummerIso.DeepRatio
import Fermat.Descent.KummerIso.Induction
import Fermat.Descent.KummerIso.SecondCase
import Fermat.Descent.KummerIso.ValidatedSecondCase
import Fermat.Descent.KummerIso.FermatEquationSevenDBruteForce
import Fermat.Descent.KummerIso.ResidueRegressions
import Fermat.Descent.KummerIso.FixedExponent
import Fermat.Descent.KummerIso.Regressions

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
`ValidatedSecondCase` exposes a prime-generic Case-II endpoint conditional
on the explicit `MorishimaConjectureAt p` proposition, through the separately
named equation-(7d) and canonical derivative-source seams.
`FermatEquationSevenDBruteForce` removes the equation-(7d) seam for any
fixed prime carrying a kernel-checked circular-unit residue certificate; its
fixed unit-system/channel route also bypasses Morishima and the derivative
source.
`ResidueRegressions` closes that route at all nine completed campaign
exponents from `37` through `1381`.
`Induction` records the conditional regular-style adapter: once the
displayed unit-ratio depth premise is supplied, it absorbs the resulting
`p`-th root and removes the left-hand weights from the equation.
`Regressions` checks the common construction at the nine completed
fixed exponents from `37` through `1381`.

See `Fermat/KummerIso/README.md` for the dependency map and the exact
remaining boundary for direct reuse of the regular-style weighted witness.
-/
