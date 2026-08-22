import Fermat.Exponents.SixHundredNinetyOne.CircularUnitCorrelationChunk7
import Fermat.Exponents.SixHundredNinetyOne.CircularUnitCorrelationChunk7B

/-!
# Cyclic-correlation data at exponent 691: residues 276--293

This is one independently compilable block of the finite correlation
certificate.
-/

namespace Fermat.SixHundredNinetyOne.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredNinetyOne.CircularUnitCyclic
open Fermat.SixHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem phase_correlation_chunk8 (d : Cyc)
    (hlo : 276 ≤ d.val) (hhi : d.val < 294) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  decide +revert

end

end Fermat.SixHundredNinetyOne.CircularUnitCertificate
