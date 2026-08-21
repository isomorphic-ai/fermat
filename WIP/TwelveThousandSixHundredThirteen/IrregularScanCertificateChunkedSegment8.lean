import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock64
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock65
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock66
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock67
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock68
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock69
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock70
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock71

/-!
# Balanced low-scan segment 8

This segment joins block certificates `64` through
`71` over coordinates
`[3200, 3600)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_64_66_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3200 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3200 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3200) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block64_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block65_chunked)
      i

private theorem scanCertificate_blocks_66_68_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3300 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3300 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3300) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block66_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block67_chunked)
      i

private theorem scanCertificate_blocks_64_68_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3200 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3200 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3200) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_64_66_chunked)
      (hright := scanCertificate_blocks_66_68_chunked)
      i

private theorem scanCertificate_blocks_68_70_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3400 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3400 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3400) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block68_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block69_chunked)
      i

private theorem scanCertificate_blocks_70_72_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3500 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3500 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3500) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block70_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block71_chunked)
      i

private theorem scanCertificate_blocks_68_72_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3400 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3400 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3400) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_68_70_chunked)
      (hright := scanCertificate_blocks_70_72_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment8_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3200 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3200 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3200) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_64_68_chunked)
      (hright := scanCertificate_blocks_68_72_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
