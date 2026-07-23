import Fermat.OneHundredFiftySeven.CircularUnitEntryCertificate.Block7

/-! # Rows 56--62 of the exponent-157 circular-unit entry certificate -/

namespace Fermat.OneHundredFiftySeven.CircularUnitEntryCertificate.Internal

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

local instance : Fact (Nat.Prime 157) :=
  ⟨Fermat.OneHundredFiftySeven.prime_157⟩
local instance : Fact (Nat.Prime 7537) :=
  ⟨Fermat.OneHundredFiftySeven.FoldCertificates.prime_7537⟩

theorem entryBlock8 (row : Fin 7) (i : Fin 77) :
    entryStatement (rowAt 8 row) i := by
  unfold entryStatement
  rw [Fermat.Irregular.CircularUnitResidues.normalizedUnitValue, div_pow]
  apply (div_eq_iff ?_).2
  · decide +kernel +revert
  · decide +kernel +revert

end Fermat.OneHundredFiftySeven.CircularUnitEntryCertificate.Internal
