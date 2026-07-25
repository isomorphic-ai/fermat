import Fermat.OneThousandFiftyOne.RegularityCertificateChunk7

namespace Fermat.OneThousandFiftyOne.RegularityCertificate

open Fermat.Irregular.ModularBernoulliScan

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1100

theorem scanResidue_ne_zero_chunk8
    (i : Fin 50) :
    scanResidue 1051 7
      (scanIndex (offsetIndex 400 50 (by omega) i)) ≠ 0 := by
  decide +revert

end Fermat.OneThousandFiftyOne.RegularityCertificate
