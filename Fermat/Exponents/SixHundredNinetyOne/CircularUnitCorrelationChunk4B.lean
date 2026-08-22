import Fermat.Exponents.SixHundredNinetyOne.CircularUnitCorrelationChunk3
import Fermat.Exponents.SixHundredNinetyOne.CircularUnitCorrelationChunk3B

/-!
# Cyclic-correlation data at exponent 691: residues 156--172
-/

namespace Fermat.SixHundredNinetyOne.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredNinetyOne.CircularUnitCyclic
open Fermat.SixHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem phase_correlation_chunk4B (d : Cyc)
    (hlo : 156 ≤ d.val) (hhi : d.val < 173) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  decide +revert

end

end Fermat.SixHundredNinetyOne.CircularUnitCertificate
