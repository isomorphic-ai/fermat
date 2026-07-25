import Fermat.SixHundredNinetyOne.CircularUnitCorrelationChunk6
import Fermat.SixHundredNinetyOne.CircularUnitCorrelationChunk6B

/-!
# Cyclic-correlation data at exponent 691: residues 259--275
-/

namespace Fermat.SixHundredNinetyOne.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredNinetyOne.CircularUnitCyclic
open Fermat.SixHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem phase_correlation_chunk7B (d : Cyc)
    (hlo : 259 ≤ d.val) (hhi : d.val < 276) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  decide +revert

end

end Fermat.SixHundredNinetyOne.CircularUnitCertificate
