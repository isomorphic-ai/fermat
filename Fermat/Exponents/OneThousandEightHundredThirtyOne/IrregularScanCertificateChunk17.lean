import Fermat.Exponents.OneThousandEightHundredThirtyOne.IrregularScanCertificateChunk16

namespace Fermat.OneThousandEightHundredThirtyOne.IrregularScan

open Fermat.Irregular.ModularBernoulliScan

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1850

theorem scanResidue_zero_only_at_channel_chunk17
    (i : Fin 50) :
    scanResidue 1831 3 (scanIndex (offsetIndex 850 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 850 50 (by omega) i) = 1274 := by
  decide +revert

end Fermat.OneThousandEightHundredThirtyOne.IrregularScan
