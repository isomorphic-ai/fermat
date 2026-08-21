import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock96
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock97
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock98
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock99
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock100
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock101
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock102
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock103

/-!
# Balanced low-scan segment 12

This segment joins block certificates `96` through
`103` over coordinates
`[4800, 5200)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_96_98_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4800 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4800 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4800) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block96_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block97_chunked)
      i

private theorem scanCertificate_blocks_98_100_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4900 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4900 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4900) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block98_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block99_chunked)
      i

private theorem scanCertificate_blocks_96_100_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4800 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4800 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4800) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_96_98_chunked)
      (hright := scanCertificate_blocks_98_100_chunked)
      i

private theorem scanCertificate_blocks_100_102_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5000 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5000 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5000) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block100_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block101_chunked)
      i

private theorem scanCertificate_blocks_102_104_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5100 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5100 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5100) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block102_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block103_chunked)
      i

private theorem scanCertificate_blocks_100_104_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5000 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5000 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5000) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_100_102_chunked)
      (hright := scanCertificate_blocks_102_104_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment12_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4800 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4800 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4800) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_96_100_chunked)
      (hright := scanCertificate_blocks_100_104_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
