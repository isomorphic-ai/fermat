import Fermat.SixHundredNinetyOne.CircularUnitCorrelationChunk2
import Fermat.SixHundredNinetyOne.CircularUnitCorrelationChunk2B

/-!
# Cyclic-correlation data at exponent 691: residues 121--137
-/

namespace Fermat.SixHundredNinetyOne.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredNinetyOne.CircularUnitCyclic
open Fermat.SixHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem phase_correlation_chunk3B (d : Cyc)
    (hlo : 121 ≤ d.val) (hhi : d.val < 138) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  decide +revert

end

end Fermat.SixHundredNinetyOne.CircularUnitCertificate
