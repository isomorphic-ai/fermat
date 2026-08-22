import Fermat.Exponents.SixHundredNinetyOne.CircularUnitCorrelationChunk8
import Fermat.Exponents.SixHundredNinetyOne.CircularUnitCorrelationChunk8B

/-!
# Cyclic-correlation data at exponent 691: residues 311--327

This is one independently compilable block of the finite correlation
certificate.
-/

namespace Fermat.SixHundredNinetyOne.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredNinetyOne.CircularUnitCyclic
open Fermat.SixHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem phase_correlation_chunk9 (d : Cyc)
    (hlo : 311 ≤ d.val) (hhi : d.val < 328) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  decide +revert

end

end Fermat.SixHundredNinetyOne.CircularUnitCertificate
