import Fermat.SixHundredNinetyOne.CircularUnitCorrelationChunk0

/-!
# Cyclic-correlation data at exponent 691: residues 52--68
-/

namespace Fermat.SixHundredNinetyOne.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredNinetyOne.CircularUnitCyclic
open Fermat.SixHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem phase_correlation_chunk1B (d : Cyc)
    (hlo : 52 ≤ d.val) (hhi : d.val < 69) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  decide +revert

end

end Fermat.SixHundredNinetyOne.CircularUnitCertificate
