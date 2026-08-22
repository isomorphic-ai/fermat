import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 112

This block covers scan coordinates `[5600, 5650)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5600, 5650)`. -/
def block112ExpectedResidues_chunked : List (ZMod 12613) :=
  [11220, 5991, 4293, 1824, 9343, 5424, 6110, 8984, 1573, 1419,
    5304, 7160, 88, 1004, 4599, 3258, 10436, 41, 8680, 6718,
    2775, 10824, 8992, 668, 3865, 9702, 10005, 9767, 9503, 4753,
    7018, 7426, 6099, 7402, 9942, 11525, 9302, 9196, 195, 6896,
    231, 12303, 11397, 8718, 3402, 1695, 1809, 6862, 3419, 10414]

/-- The one batched computation certificate for block 112. -/
theorem scanBlockResidues_block112_eq_chunked :
    scanBlockResidues 5600 50 = block112ExpectedResidues_chunked := by
  decide

private theorem block112ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block112ExpectedResidues_chunked[i.val]'(by
        simp [block112ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5600 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 112 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block112_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5600 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5600 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5600) (width := 50) (hbound := by omega)
      (expected := block112ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block112_eq_chunked)
      (hzeroCandidates := block112ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
