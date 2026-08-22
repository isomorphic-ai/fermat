import Fermat.Exponents.SixHundredNinetyOne.CircularUnitCorrelationChunk4
import Fermat.Exponents.SixHundredNinetyOne.CircularUnitCorrelationChunk4B

/-!
# Cyclic-correlation data at exponent 691: residues 173--189

This is one independently compilable block of the finite correlation
certificate.
-/

namespace Fermat.SixHundredNinetyOne.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredNinetyOne.CircularUnitCyclic
open Fermat.SixHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem phase_correlation_chunk5 (d : Cyc)
    (hlo : 173 ≤ d.val) (hhi : d.val < 190) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  decide +revert

end

end Fermat.SixHundredNinetyOne.CircularUnitCertificate
