import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock48
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock49
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock50
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock51
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock52
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock53
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock54
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock55

/-!
# Balanced low-scan segment 6

This segment joins block certificates `48` through
`55` over coordinates
`[2400, 2800)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_48_50_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2400 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2400 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2400) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block48_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block49_chunked)
      i

private theorem scanCertificate_blocks_50_52_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2500 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2500 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2500) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block50_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block51_chunked)
      i

private theorem scanCertificate_blocks_48_52_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2400 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2400 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2400) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_48_50_chunked)
      (hright := scanCertificate_blocks_50_52_chunked)
      i

private theorem scanCertificate_blocks_52_54_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2600 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2600 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2600) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block52_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block53_chunked)
      i

private theorem scanCertificate_blocks_54_56_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2700 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2700 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2700) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block54_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block55_chunked)
      i

private theorem scanCertificate_blocks_52_56_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2600 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2600 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2600) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_52_54_chunked)
      (hright := scanCertificate_blocks_54_56_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment6_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2400 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2400 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2400) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_48_52_chunked)
      (hright := scanCertificate_blocks_52_56_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
