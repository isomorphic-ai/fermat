import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock80
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock81
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock82
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock83
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock84
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock85
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock86
import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedBlock87

/-!
# Balanced low-scan segment 10

This segment joins block certificates `80` through
`87` over coordinates
`[4000, 4400)`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_blocks_80_82_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4000 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4000 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4000) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block80_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block81_chunked)
      i

private theorem scanCertificate_blocks_82_84_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4100 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4100 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4100) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block82_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block83_chunked)
      i

private theorem scanCertificate_blocks_80_84_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4000 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4000 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4000) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_80_82_chunked)
      (hright := scanCertificate_blocks_82_84_chunked)
      i

private theorem scanCertificate_blocks_84_86_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4200 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4200 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4200) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block84_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block85_chunked)
      i

private theorem scanCertificate_blocks_86_88_chunked
    (i : Fin 100) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4300 100 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4300 100 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4300) (leftWidth := 50)
      (rightWidth := 50) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_block86_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_block87_chunked)
      i

private theorem scanCertificate_blocks_84_88_chunked
    (i : Fin 200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4200 200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4200 200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4200) (leftWidth := 100)
      (rightWidth := 100) (hbound := by omega)
      (hleft := scanCertificate_blocks_84_86_chunked)
      (hright := scanCertificate_blocks_86_88_chunked)
      i

theorem scanResidue_zero_imp_mem_irregularCandidates_segment10_chunked
    (i : Fin 400) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4000 400 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4000 400 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4000) (leftWidth := 200)
      (rightWidth := 200) (hbound := by omega)
      (hleft := scanCertificate_blocks_80_84_chunked)
      (hright := scanCertificate_blocks_84_88_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
