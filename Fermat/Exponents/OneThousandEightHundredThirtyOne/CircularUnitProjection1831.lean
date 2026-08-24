import Fermat.Descent.Irregular.CanonicalKummerChannel

/-!
# Intrinsic Case-II.1 projection at exponent 1831

The possible irregular Bernoulli index `1274` selects Kummer row `636`.
This module records that row and its canonical projection using only
`p = 1831`; no auxiliary split prime, residue root, or finite-field phase
occurs in the definition.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitProjection

noncomputable section

set_option maxRecDepth 100000

open Fermat.Irregular.AuxiliaryResidueChannels
open KummerCriterion.CyclotomicUnits

local instance : Fact (Nat.Prime 1831) := ⟨by decide⟩

/-- Zero-based Kummer row corresponding to Bernoulli index `1274`. -/
def irregularKummerRow : Fin (kummerLogRank 1831) := 636

/-- The intrinsic Case-II.1 character projection at the possible irregular
row. Its coefficients are determined entirely by `p = 1831`. -/
def projection (e : Fin (kummerLogRank 1831) → ZMod 1831) : ZMod 1831 :=
  canonicalKummerChannel 1831 (by norm_num) irregularKummerRow e

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitProjection
