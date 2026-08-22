import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock24
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock25
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock26
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock27
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock28
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock29
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock30
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock31

/-!
# Balanced low-scan segment 3

This segment joins block certificates `24` through
`31` over coordinates
`[1200, 1600)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_24_26_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1200 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1200 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1200) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block24_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block25_chunked)
      i

private theorem scanCertificate_blocks_26_28_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1300 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1300 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1300) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block26_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block27_chunked)
      i

private theorem scanCertificate_blocks_24_28_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1200 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1200 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1200) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_24_26_chunked)
      (hright := scanCertificate_blocks_26_28_chunked)
      i

private theorem scanCertificate_blocks_28_30_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1400 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1400 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1400) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block28_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block29_chunked)
      i

private theorem scanCertificate_blocks_30_32_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1500 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1500 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1500) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block30_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block31_chunked)
      i

private theorem scanCertificate_blocks_28_32_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1400 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1400 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1400) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_28_30_chunked)
      (hright := scanCertificate_blocks_30_32_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment3_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1200 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1200 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1200) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_24_28_chunked)
      (hright := scanCertificate_blocks_28_32_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
