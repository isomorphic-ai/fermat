import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock120
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock121
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock122
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock123
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock124
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock125
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock126

/-!
# Balanced low-scan segment 15

This segment joins block certificates `120` through
`126` over coordinates
`[6000, 6305)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_121_123_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 6050 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 6050 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 6050) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block121_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block122_chunked)
      i

private theorem scanCertificate_blocks_120_123_chunked
    (i : Fin 150) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 6000 150 (by omega) i)) = 0 →
      scanIndex (offsetIndex 6000 150 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 6000) (leftWidth := 50)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block120_chunked)
      (hright := scanCertificate_blocks_121_123_chunked)
      i

private theorem scanCertificate_blocks_123_125_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 6150 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 6150 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 6150) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block123_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block124_chunked)
      i

private theorem scanCertificate_blocks_125_127_chunked
    (i : Fin 55) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 6250 55 (by omega) i)) = 0 →
      scanIndex (offsetIndex 6250 55 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 6250) (leftWidth := 50)
      (rightWidth := 5) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block125_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block126_chunked)
      i

private theorem scanCertificate_blocks_123_127_chunked
    (i : Fin 155) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 6150 155 (by omega) i)) = 0 →
      scanIndex (offsetIndex 6150 155 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 6150) (leftWidth := 100)
      (rightWidth := 55) (hbound := by omega)
      (hleft := scanCertificate_blocks_123_125_chunked)
      (hright := scanCertificate_blocks_125_127_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment15_chunked
    (i : Fin 305) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 6000 305 (by omega) i)) = 0 →
      scanIndex (offsetIndex 6000 305 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 6000) (leftWidth := 150)
      (rightWidth := 155) (hbound := by omega)
      (hleft := scanCertificate_blocks_120_123_chunked)
      (hright := scanCertificate_blocks_123_127_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
