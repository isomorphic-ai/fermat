import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 67

This block covers scan coordinates `[3350, 3400)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3350, 3400)`. -/
def block67ExpectedResidues_chunked : List (ZMod 12613) :=
  [1228, 9670, 7147, 9798, 6154, 11739, 8635, 12317, 5622, 1132,
    7987, 9652, 6316, 404, 12198, 6030, 6382, 1130, 1959, 12269,
    11421, 9456, 3566, 2492, 4805, 3357, 11306, 5209, 7135, 4037,
    1498, 10274, 6274, 9878, 1861, 5500, 2136, 1953, 9575, 9882,
    7825, 11517, 9423, 2215, 8974, 37, 4575, 11476, 7198, 5670]

/-- The one batched computation certificate for block 67. -/
theorem scanBlockResidues_block67_eq_chunked :
    scanBlockResidues 3350 50 = block67ExpectedResidues_chunked := by
  decide

private theorem block67ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block67ExpectedResidues_chunked[i.val]'(by
        simp [block67ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3350 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 67 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block67_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3350 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3350 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3350) (width := 50) (hbound := by omega)
      (expected := block67ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block67_eq_chunked)
      (hzeroCandidates := block67ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
