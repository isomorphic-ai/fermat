import Fermat.Exponents.SixHundredNinetyOne.CircularUnitCorrelationChunk5
import Fermat.Exponents.SixHundredNinetyOne.CircularUnitCorrelationChunk5B

/-!
# Cyclic-correlation data at exponent 691: residues 225--241
-/

namespace Fermat.SixHundredNinetyOne.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredNinetyOne.CircularUnitCyclic
open Fermat.SixHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem phase_correlation_chunk6B (d : Cyc)
    (hlo : 225 ≤ d.val) (hhi : d.val < 242) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  decide +revert

end

end Fermat.SixHundredNinetyOne.CircularUnitCertificate
