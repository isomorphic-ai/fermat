import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock56
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock57
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock58
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock59
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock60
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock61
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock62
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock63

/-!
# Balanced low-scan segment 7

This segment joins block certificates `56` through
`63` over coordinates
`[2800, 3200)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_56_58_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2800 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2800 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2800) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block56_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block57_chunked)
      i

private theorem scanCertificate_blocks_58_60_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2900 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2900 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2900) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block58_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block59_chunked)
      i

private theorem scanCertificate_blocks_56_60_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2800 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2800 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2800) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_56_58_chunked)
      (hright := scanCertificate_blocks_58_60_chunked)
      i

private theorem scanCertificate_blocks_60_62_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3000 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3000 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3000) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block60_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block61_chunked)
      i

private theorem scanCertificate_blocks_62_64_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3100 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3100 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3100) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block62_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block63_chunked)
      i

private theorem scanCertificate_blocks_60_64_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3000 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3000 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3000) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_60_62_chunked)
      (hright := scanCertificate_blocks_62_64_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment7_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2800 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2800 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2800) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_56_60_chunked)
      (hright := scanCertificate_blocks_60_64_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
