import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedAssemblyCore
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment0
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment1
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment2
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment3
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment4
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment5
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment6
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment7
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment8
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment9
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment10
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment11
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment12
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment13
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment14
import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedSegment15

/-!
# Balanced assembly of the complete chunked exponent-12613 low scan

Sixteen segment certificates are joined through a balanced binary tree.
The public endpoint removes the identity `offsetIndex 0 6305`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

private theorem scanCertificate_segments_0_2_chunked
    (i : Fin 800) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 0 800 (by omega) i)) = 0 →
      scanIndex (offsetIndex 0 800 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 0) (leftWidth := 400)
      (rightWidth := 400) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_segment0_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_segment1_chunked)
      i

private theorem scanCertificate_segments_2_4_chunked
    (i : Fin 800) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 800 800 (by omega) i)) = 0 →
      scanIndex (offsetIndex 800 800 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 800) (leftWidth := 400)
      (rightWidth := 400) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_segment2_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_segment3_chunked)
      i

private theorem scanCertificate_segments_0_4_chunked
    (i : Fin 1600) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 0 1600 (by omega) i)) = 0 →
      scanIndex (offsetIndex 0 1600 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 0) (leftWidth := 800)
      (rightWidth := 800) (hbound := by omega)
      (hleft := scanCertificate_segments_0_2_chunked)
      (hright := scanCertificate_segments_2_4_chunked)
      i

private theorem scanCertificate_segments_4_6_chunked
    (i : Fin 800) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1600 800 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1600 800 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1600) (leftWidth := 400)
      (rightWidth := 400) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_segment4_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_segment5_chunked)
      i

private theorem scanCertificate_segments_6_8_chunked
    (i : Fin 800) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2400 800 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2400 800 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 2400) (leftWidth := 400)
      (rightWidth := 400) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_segment6_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_segment7_chunked)
      i

private theorem scanCertificate_segments_4_8_chunked
    (i : Fin 1600) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1600 1600 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1600 1600 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 1600) (leftWidth := 800)
      (rightWidth := 800) (hbound := by omega)
      (hleft := scanCertificate_segments_4_6_chunked)
      (hright := scanCertificate_segments_6_8_chunked)
      i

private theorem scanCertificate_segments_0_8_chunked
    (i : Fin 3200) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 0 3200 (by omega) i)) = 0 →
      scanIndex (offsetIndex 0 3200 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 0) (leftWidth := 1600)
      (rightWidth := 1600) (hbound := by omega)
      (hleft := scanCertificate_segments_0_4_chunked)
      (hright := scanCertificate_segments_4_8_chunked)
      i

private theorem scanCertificate_segments_8_10_chunked
    (i : Fin 800) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3200 800 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3200 800 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3200) (leftWidth := 400)
      (rightWidth := 400) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_segment8_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_segment9_chunked)
      i

private theorem scanCertificate_segments_10_12_chunked
    (i : Fin 800) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4000 800 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4000 800 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4000) (leftWidth := 400)
      (rightWidth := 400) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_segment10_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_segment11_chunked)
      i

private theorem scanCertificate_segments_8_12_chunked
    (i : Fin 1600) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3200 1600 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3200 1600 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3200) (leftWidth := 800)
      (rightWidth := 800) (hbound := by omega)
      (hleft := scanCertificate_segments_8_10_chunked)
      (hright := scanCertificate_segments_10_12_chunked)
      i

private theorem scanCertificate_segments_12_14_chunked
    (i : Fin 800) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4800 800 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4800 800 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4800) (leftWidth := 400)
      (rightWidth := 400) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_segment12_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_segment13_chunked)
      i

private theorem scanCertificate_segments_14_16_chunked
    (i : Fin 705) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5600 705 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5600 705 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 5600) (leftWidth := 400)
      (rightWidth := 305) (hbound := by omega)
      (hleft := scanResidue_zero_imp_mem_irregularCandidates_segment14_chunked)
      (hright := scanResidue_zero_imp_mem_irregularCandidates_segment15_chunked)
      i

private theorem scanCertificate_segments_12_16_chunked
    (i : Fin 1505) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4800 1505 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4800 1505 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 4800) (leftWidth := 800)
      (rightWidth := 705) (hbound := by omega)
      (hleft := scanCertificate_segments_12_14_chunked)
      (hright := scanCertificate_segments_14_16_chunked)
      i

private theorem scanCertificate_segments_8_16_chunked
    (i : Fin 3105) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3200 3105 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3200 3105 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 3200) (leftWidth := 1600)
      (rightWidth := 1505) (hbound := by omega)
      (hleft := scanCertificate_segments_8_12_chunked)
      (hright := scanCertificate_segments_12_16_chunked)
      i

theorem scanCertificate_all_segments_chunked
    (i : Fin 6305) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 0 6305 (by omega) i)) = 0 →
      scanIndex (offsetIndex 0 6305 (by omega) i) ∈
        irregularCandidates := by
  exact
    combineAdjacentScanCertificates_chunked
      (offset := 0) (leftWidth := 3200)
      (rightWidth := 3105) (hbound := by omega)
      (hleft := scanCertificate_segments_0_8_chunked)
      (hright := scanCertificate_segments_8_16_chunked)
      i

/-- A zero residue at any of the `6305` scan coordinates belongs to the
four reported irregular candidates. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_chunked
    (i : Fin 6305) :
    scanResidue 12613 2 (scanIndex i) = 0 →
      scanIndex i ∈ irregularCandidates := by
  have hindex : offsetIndex 0 6305 (by omega) i = i := by
    apply Fin.ext
    simp [offsetIndex]
  simpa only [hindex] using scanCertificate_all_segments_chunked i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
