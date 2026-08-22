import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Binary assembly helper for the chunked exponent-12613 low scan

Two certificates on adjacent coordinate ranges combine into one certificate
on their union.  Generated segment and final assemblies use this theorem as
a balanced binary tree, avoiding a single 127-way case split.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

/-- Combine zero-to-candidate certificates on two adjacent scan ranges. -/
theorem combineAdjacentScanCertificates_chunked
    (offset leftWidth rightWidth : ℕ)
    (hbound : offset + (leftWidth + rightWidth) ≤ 6305)
    (hleft :
      ∀ i : Fin leftWidth,
        scanResidue 12613 2
            (scanIndex
              (offsetIndex offset leftWidth (by omega) i)) = 0 →
          scanIndex (offsetIndex offset leftWidth (by omega) i) ∈
            irregularCandidates)
    (hright :
      ∀ i : Fin rightWidth,
        scanResidue 12613 2
            (scanIndex
              (offsetIndex (offset + leftWidth) rightWidth
                (by omega) i)) = 0 →
          scanIndex
              (offsetIndex (offset + leftWidth) rightWidth
                (by omega) i) ∈ irregularCandidates)
    (i : Fin (leftWidth + rightWidth)) :
    scanResidue 12613 2
        (scanIndex
          (offsetIndex offset (leftWidth + rightWidth) hbound i)) = 0 →
      scanIndex
          (offsetIndex offset (leftWidth + rightWidth) hbound i) ∈
        irregularCandidates := by
  by_cases hleftIndex : i.val < leftWidth
  · let j : Fin leftWidth := ⟨i.val, hleftIndex⟩
    have hij :
        offsetIndex offset (leftWidth + rightWidth) hbound i =
          offsetIndex offset leftWidth (by omega) j := by
      apply Fin.ext
      simp [offsetIndex, j]
    simpa only [hij] using hleft j
  · let j : Fin rightWidth := ⟨i.val - leftWidth, by omega⟩
    have hij :
        offsetIndex offset (leftWidth + rightWidth) hbound i =
          offsetIndex (offset + leftWidth) rightWidth
            (by omega) j := by
      apply Fin.ext
      simp [offsetIndex, j]
      omega
    simpa only [hij] using hright j

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
