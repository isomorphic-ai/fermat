import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock0
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock1
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock2
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock3
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock4
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock5
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock6
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock7

/-!
# Balanced low-scan segment 0

This segment joins block certificates `0` through
`7` over coordinates
`[0, 400)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_0_2_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 0 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 0 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 0) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block0_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block1_chunked)
      i

private theorem scanCertificate_blocks_2_4_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 100 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 100 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 100) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block2_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block3_chunked)
      i

private theorem scanCertificate_blocks_0_4_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 0 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 0 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 0) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_0_2_chunked)
      (hright := scanCertificate_blocks_2_4_chunked)
      i

private theorem scanCertificate_blocks_4_6_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 200 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 200 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 200) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block4_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block5_chunked)
      i

private theorem scanCertificate_blocks_6_8_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 300 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 300 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 300) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block6_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block7_chunked)
      i

private theorem scanCertificate_blocks_4_8_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 200 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 200 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 200) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_4_6_chunked)
      (hright := scanCertificate_blocks_6_8_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment0_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 0 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 0 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 0) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_0_4_chunked)
      (hright := scanCertificate_blocks_4_8_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
