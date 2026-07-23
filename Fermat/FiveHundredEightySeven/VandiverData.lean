import Fermat.Irregular.VandiverData
import Fermat.FiveHundredEightySeven.IrregularScan

/-!
# Vandiver's finite Bernoulli condition at exponent 587

The complete modular Voronoi scan leaves exactly the two irregular indices
`90` and `92`. Direct Faulhaber certificates at the lifted indices
`90 * 587 = 52830` and `92 * 587 = 54004` exclude a third factor of `587`
from both lifted Bernoulli numerators.

This module exposes that kernel-checked finite arithmetic through the common
`BernoulliCubeCondition` API consumed by Vandiver's historical Lemma II.  It
does not by itself assert the global second-case descent.
-/

namespace Fermat.FiveHundredEightySeven.VandiverData

open Fermat.Irregular.VandiverData

local instance : Fact (Nat.Prime 587) := ⟨by norm_num⟩

/-- Every indexed Bernoulli numerator in Vandiver's finite condition is
checked at exponent `587`. -/
theorem bernoulliCubeCondition_fiveHundredEightySeven :
    BernoulliCubeCondition 587 :=
  Fermat.FiveHundredEightySeven.IrregularScan.bernoulliCubeCondition_fiveHundredEightySeven

/-- Numeric-name alias for campaign consumers. -/
theorem bernoulliCubeCondition_587 :
    BernoulliCubeCondition 587 :=
  bernoulliCubeCondition_fiveHundredEightySeven

end Fermat.FiveHundredEightySeven.VandiverData
