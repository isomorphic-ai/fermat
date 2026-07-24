import Fermat.OneHundredFiftySeven.CircularUnitEntryCertificate.Block2

/-! # Rows 21--27 of the exponent-157 circular-unit entry certificate -/

namespace Fermat.OneHundredFiftySeven.CircularUnitEntryCertificate.Internal

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 157) :=
  ⟨Fermat.OneHundredFiftySeven.prime_157⟩
local instance : Fact (Nat.Prime 7537) :=
  ⟨Fermat.OneHundredFiftySeven.FoldCertificates.prime_7537⟩

theorem entryBlock3 (row : Fin 7) (i : Fin 77) :
    entryStatement (rowAt 3 row) i := by
  unfold entryStatement
  rw [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue, div_pow]
  apply (div_eq_iff ?_).2
  · decide +kernel +revert
  · decide +kernel +revert

end Fermat.OneHundredFiftySeven.CircularUnitEntryCertificate.Internal
