import Fermat.Irregular.ModularBernoulliScan

/-!
# Finite Voronoi scan certificate at exponent 229

The paired 1381/1831 proof package uses `229` as the regular support
exponent for the neighbor `1832 = 8 * 229`.  This module isolates the
complete finite computation behind that provision.

There are exactly `113` even indices in Kummer's range
`2 ≤ k ≤ 226`.  The theorem below evaluates the depth-one Voronoi residue
at all of them in the kernel.  Base `6` is the full-order Lucas witness
recorded by the package and, in particular, is coprime to `229`.
-/

namespace Fermat.TwoHundredTwentyNine.RegularityCertificate

open Fermat.Irregular.ModularBernoulliScan

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 250

/-- The `i`-th even index in the classical range `2 ≤ k ≤ 226`. -/
def scanIndex (i : Fin 113) : ℕ := 2 * (i + 1)

/-- Every depth-one Voronoi residue in the regularity range is nonzero
modulo `229`. -/
theorem scanResidue_ne_zero (i : Fin 113) :
    scanResidue 229 6 (scanIndex i) ≠ 0 := by
  decide +revert

end Fermat.TwoHundredTwentyNine.RegularityCertificate
