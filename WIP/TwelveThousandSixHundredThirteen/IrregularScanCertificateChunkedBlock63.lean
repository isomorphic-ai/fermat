import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 63

This block covers scan coordinates `[3150, 3200)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3150, 3200)`. -/
def block63ExpectedResidues_chunked : List (ZMod 12613) :=
  [8938, 10379, 631, 9295, 5598, 840, 2275, 7815, 10637, 11955,
    5182, 9802, 5500, 6103, 7203, 10507, 5060, 2456, 10678, 1726,
    439, 5766, 8067, 8129, 5293, 1278, 11057, 5975, 10123, 979,
    5276, 5692, 5043, 1364, 5403, 11128, 1762, 2853, 5325, 3520,
    5209, 3377, 4341, 6184, 1680, 5639, 3979, 8427, 6827, 4453]

/-- The one batched computation certificate for block 63. -/
theorem scanBlockResidues_block63_eq_chunked :
    scanBlockResidues 3150 50 = block63ExpectedResidues_chunked := by
  decide

private theorem block63ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block63ExpectedResidues_chunked[i.val]'(by
        simp [block63ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3150 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 63 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block63_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3150 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3150 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3150) (width := 50) (hbound := by omega)
      (expected := block63ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block63_eq_chunked)
      (hzeroCandidates := block63ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
