import Fermat.SixHundredNinetyOne.CircularUnitCorrelationChunk8
import Fermat.SixHundredNinetyOne.CircularUnitCorrelationChunk8B

/-!
# Cyclic-correlation data at exponent 691: residues 328--344
-/

namespace Fermat.SixHundredNinetyOne.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredNinetyOne.CircularUnitCyclic
open Fermat.SixHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem phase_correlation_chunk9B (d : Cyc) (hlo : 328 ≤ d.val) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  decide +revert

end

end Fermat.SixHundredNinetyOne.CircularUnitCertificate
