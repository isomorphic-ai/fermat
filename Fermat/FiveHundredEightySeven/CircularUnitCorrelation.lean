import Fermat.FiveHundredEightySeven.CircularUnitMatrix

/-!
# Finite cyclic-correlation data at exponent 587

This module isolates the moderately expensive kernel computation certifying
the 293 cyclic correlations.  Keeping it separate lets downstream algebraic
changes reuse the compiled finite proof.
-/

namespace Fermat.FiveHundredEightySeven.CircularUnitCertificate

noncomputable section

open Fermat.FiveHundredEightySeven.CircularUnitCyclic
open Fermat.FiveHundredEightySeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Kernel-checked cyclic-correlation certificate.  This is the compressed
finite replacement for 85,264 dense inverse entries. -/
theorem phase_correlation (d : Cyc) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  decide +revert

end

end Fermat.FiveHundredEightySeven.CircularUnitCertificate
