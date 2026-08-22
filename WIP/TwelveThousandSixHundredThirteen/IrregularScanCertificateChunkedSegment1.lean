import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock8
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock9
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock10
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock11
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock12
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock13
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock14
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock15

/-!
# Balanced low-scan segment 1

This segment joins block certificates `8` through
`15` over coordinates
`[400, 800)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_8_10_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 400 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 400 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 400) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block8_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block9_chunked)
      i

private theorem scanCertificate_blocks_10_12_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 500 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 500 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 500) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block10_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block11_chunked)
      i

private theorem scanCertificate_blocks_8_12_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 400 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 400 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 400) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_8_10_chunked)
      (hright := scanCertificate_blocks_10_12_chunked)
      i

private theorem scanCertificate_blocks_12_14_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 600 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 600 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 600) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block12_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block13_chunked)
      i

private theorem scanCertificate_blocks_14_16_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 700 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 700 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 700) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block14_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block15_chunked)
      i

private theorem scanCertificate_blocks_12_16_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 600 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 600 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 600) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_12_14_chunked)
      (hright := scanCertificate_blocks_14_16_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment1_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 400 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 400 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 400) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_8_12_chunked)
      (hright := scanCertificate_blocks_12_16_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
