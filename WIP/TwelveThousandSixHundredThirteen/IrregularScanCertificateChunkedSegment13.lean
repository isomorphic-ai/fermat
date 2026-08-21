import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock104
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock105
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock106
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock107
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock108
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock109
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock110
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock111

/-!
# Balanced low-scan segment 13

This segment joins block certificates `104` through
`111` over coordinates
`[5200, 5600)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_104_106_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5200 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5200 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5200) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block104_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block105_chunked)
      i

private theorem scanCertificate_blocks_106_108_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5300 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5300 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5300) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block106_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block107_chunked)
      i

private theorem scanCertificate_blocks_104_108_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5200 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5200 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5200) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_104_106_chunked)
      (hright := scanCertificate_blocks_106_108_chunked)
      i

private theorem scanCertificate_blocks_108_110_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5400 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5400 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5400) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block108_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block109_chunked)
      i

private theorem scanCertificate_blocks_110_112_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5500 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5500 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5500) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block110_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block111_chunked)
      i

private theorem scanCertificate_blocks_108_112_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5400 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5400 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5400) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_108_110_chunked)
      (hright := scanCertificate_blocks_110_112_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment13_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5200 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5200 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5200) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_104_108_chunked)
      (hright := scanCertificate_blocks_108_112_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
