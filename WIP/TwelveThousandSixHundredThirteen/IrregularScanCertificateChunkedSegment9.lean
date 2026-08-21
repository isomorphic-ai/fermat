import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock72
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock73
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock74
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock75
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock76
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock77
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock78
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock79

/-!
# Balanced low-scan segment 9

This segment joins block certificates `72` through
`79` over coordinates
`[3600, 4000)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_72_74_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3600 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3600 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3600) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block72_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block73_chunked)
      i

private theorem scanCertificate_blocks_74_76_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3700 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3700 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3700) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block74_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block75_chunked)
      i

private theorem scanCertificate_blocks_72_76_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3600 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3600 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3600) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_72_74_chunked)
      (hright := scanCertificate_blocks_74_76_chunked)
      i

private theorem scanCertificate_blocks_76_78_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3800 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3800 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3800) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block76_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block77_chunked)
      i

private theorem scanCertificate_blocks_78_80_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3900 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3900 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3900) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block78_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block79_chunked)
      i

private theorem scanCertificate_blocks_76_80_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3800 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3800 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3800) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_76_78_chunked)
      (hright := scanCertificate_blocks_78_80_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment9_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3600 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3600 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3600) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_72_76_chunked)
      (hright := scanCertificate_blocks_76_80_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
