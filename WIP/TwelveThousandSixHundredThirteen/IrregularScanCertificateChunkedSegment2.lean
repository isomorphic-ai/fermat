import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock16
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock17
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock18
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock19
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock20
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock21
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock22
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock23

/-!
# Balanced low-scan segment 2

This segment joins block certificates `16` through
`23` over coordinates
`[800, 1200)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_16_18_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 800 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 800 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 800) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block16_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block17_chunked)
      i

private theorem scanCertificate_blocks_18_20_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 900 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 900 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 900) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block18_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block19_chunked)
      i

private theorem scanCertificate_blocks_16_20_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 800 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 800 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 800) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_16_18_chunked)
      (hright := scanCertificate_blocks_18_20_chunked)
      i

private theorem scanCertificate_blocks_20_22_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1000 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1000 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1000) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block20_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block21_chunked)
      i

private theorem scanCertificate_blocks_22_24_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1100 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1100 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1100) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block22_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block23_chunked)
      i

private theorem scanCertificate_blocks_20_24_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1000 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1000 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1000) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_20_22_chunked)
      (hright := scanCertificate_blocks_22_24_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment2_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 800 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 800 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 800) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_16_20_chunked)
      (hright := scanCertificate_blocks_20_24_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
