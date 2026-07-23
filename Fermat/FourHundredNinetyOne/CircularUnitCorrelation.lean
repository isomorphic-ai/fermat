import Fermat.FourHundredNinetyOne.CircularUnitMatrix

/-!
# Finite cyclic-correlation data at exponent 491

This module isolates the kernel computation certifying all 245 cyclic
correlations.  It is the compressed replacement for a dense `244 × 244`
inverse certificate.
-/

namespace Fermat.FourHundredNinetyOne.CircularUnitCertificate

noncomputable section

open Fermat.FourHundredNinetyOne.CircularUnitCyclic
open Fermat.FourHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Kernel-checked cyclic-correlation certificate. -/
theorem phase_correlation (d : Cyc) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  decide +revert

end

end Fermat.FourHundredNinetyOne.CircularUnitCertificate
