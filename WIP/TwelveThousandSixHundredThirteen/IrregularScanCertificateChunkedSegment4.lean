import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock32
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock33
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock34
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock35
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock36
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock37
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock38
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock39

/-!
# Balanced low-scan segment 4

This segment joins block certificates `32` through
`39` over coordinates
`[1600, 2000)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_32_34_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1600 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1600 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1600) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block32_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block33_chunked)
      i

private theorem scanCertificate_blocks_34_36_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1700 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1700 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1700) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block34_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block35_chunked)
      i

private theorem scanCertificate_blocks_32_36_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1600 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1600 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1600) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_32_34_chunked)
      (hright := scanCertificate_blocks_34_36_chunked)
      i

private theorem scanCertificate_blocks_36_38_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1800 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1800 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1800) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block36_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block37_chunked)
      i

private theorem scanCertificate_blocks_38_40_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1900 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1900 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1900) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block38_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block39_chunked)
      i

private theorem scanCertificate_blocks_36_40_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1800 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1800 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1800) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_36_38_chunked)
      (hright := scanCertificate_blocks_38_40_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment4_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1600 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1600 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1600) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_32_36_chunked)
      (hright := scanCertificate_blocks_36_40_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
