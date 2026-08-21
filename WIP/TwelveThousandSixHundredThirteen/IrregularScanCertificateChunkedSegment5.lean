import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock40
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock41
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock42
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock43
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock44
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock45
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock46
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock47

/-!
# Balanced low-scan segment 5

This segment joins block certificates `40` through
`47` over coordinates
`[2000, 2400)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_40_42_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2000 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2000 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2000) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block40_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block41_chunked)
      i

private theorem scanCertificate_blocks_42_44_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2100 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2100 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2100) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block42_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block43_chunked)
      i

private theorem scanCertificate_blocks_40_44_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2000 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2000 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2000) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_40_42_chunked)
      (hright := scanCertificate_blocks_42_44_chunked)
      i

private theorem scanCertificate_blocks_44_46_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2200 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2200 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2200) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block44_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block45_chunked)
      i

private theorem scanCertificate_blocks_46_48_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2300 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2300 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2300) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block46_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block47_chunked)
      i

private theorem scanCertificate_blocks_44_48_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2200 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2200 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2200) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_44_46_chunked)
      (hright := scanCertificate_blocks_46_48_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment5_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2000 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2000 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2000) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_40_44_chunked)
      (hright := scanCertificate_blocks_44_48_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
