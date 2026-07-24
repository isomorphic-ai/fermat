import Fermat.OneThousandThreeHundredEightyOne.IrregularScanCertificateChunk9

namespace Fermat.OneThousandThreeHundredEightyOne.IrregularScan

open Fermat.Irregular.ModularBernoulliScan

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1400

theorem scanResidue_zero_only_at_channel_chunk10
    (i : Fin 50) :
    scanResidue 1381 2 (scanIndex (offsetIndex 500 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 500 50 (by omega) i) = 266 := by
  decide +revert

end Fermat.OneThousandThreeHundredEightyOne.IrregularScan
