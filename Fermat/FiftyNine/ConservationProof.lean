/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The statewise conservation proof at exponent 59

This small public facade exposes the completed conservation-state route
without making users import its implementation module by name.  The proof
constructs literal equation-(8) witnesses from an allocated primitive
second-case Fermat state, enters Vandiver's historical support descent, and
uses the checked Sophie--Germain computation for Case I.
-/
import Fermat.FiftyNine.Conservation.FermatStateHistoricalDescent59

namespace Fermat.FiftyNine

/-- Fermat's Last Theorem at exponent `59`, through the allocated
conservation state, literal equation (8), and strict historical support
descent. -/
theorem holdsAt_fiftyNine_stateEquationEight : Fermat.HoldsAt 59 :=
  Conservation.FermatStateHistoricalDescent59.holdsAt_fiftyNine_via_stateEquationEight

end Fermat.FiftyNine
