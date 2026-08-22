import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock88
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock89
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock90
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock91
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock92
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock93
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock94
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock95

/-!
# Balanced low-scan segment 11

This segment joins block certificates `88` through
`95` over coordinates
`[4400, 4800)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_88_90_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4400 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4400 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4400) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block88_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block89_chunked)
      i

private theorem scanCertificate_blocks_90_92_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4500 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4500 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4500) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block90_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block91_chunked)
      i

private theorem scanCertificate_blocks_88_92_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4400 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4400 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4400) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_88_90_chunked)
      (hright := scanCertificate_blocks_90_92_chunked)
      i

private theorem scanCertificate_blocks_92_94_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4600 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4600 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4600) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block92_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block93_chunked)
      i

private theorem scanCertificate_blocks_94_96_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4700 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4700 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4700) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block94_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block95_chunked)
      i

private theorem scanCertificate_blocks_92_96_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4600 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4600 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4600) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_92_94_chunked)
      (hright := scanCertificate_blocks_94_96_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment11_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4400 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4400 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4400) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_88_92_chunked)
      (hright := scanCertificate_blocks_92_96_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
