import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock112
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock113
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock114
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock115
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock116
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock117
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock118
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock119

/-!
# Balanced low-scan segment 14

This segment joins block certificates `112` through
`119` over coordinates
`[5600, 6000)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_112_114_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5600 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5600 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5600) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block112_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block113_chunked)
      i

private theorem scanCertificate_blocks_114_116_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5700 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5700 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5700) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block114_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block115_chunked)
      i

private theorem scanCertificate_blocks_112_116_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5600 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5600 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5600) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_112_114_chunked)
      (hright := scanCertificate_blocks_114_116_chunked)
      i

private theorem scanCertificate_blocks_116_118_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5800 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5800 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5800) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block116_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block117_chunked)
      i

private theorem scanCertificate_blocks_118_120_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5900 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5900 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5900) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block118_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block119_chunked)
      i

private theorem scanCertificate_blocks_116_120_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5800 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5800 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5800) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_116_118_chunked)
      (hright := scanCertificate_blocks_118_120_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment14_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5600 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5600 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5600) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_112_116_chunked)
      (hright := scanCertificate_blocks_116_120_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
