import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 113

This block covers scan coordinates `[5650, 5700)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5650, 5700)`. -/
def block113ExpectedResidues_chunked : List (ZMod 12613) :=
  [4706, 5140, 9366, 10386, 5480, 6444, 655, 10405, 4259, 7878,
    2985, 10398, 756, 10874, 10598, 1907, 3606, 9673, 7176, 9006,
    994, 5655, 10820, 6011, 155, 11995, 3263, 4685, 6811, 9986,
    11773, 800, 684, 4466, 7590, 8171, 1603, 1387, 2754, 12402,
    3787, 4458, 8622, 11617, 7219, 9930, 7042, 599, 8704, 330]

/-- The one batched computation certificate for block 113. -/
theorem scanBlockResidues_block113_eq_chunked :
    scanBlockResidues 5650 50 = block113ExpectedResidues_chunked := by
  decide

private theorem block113ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block113ExpectedResidues_chunked[i.val]'(by
        simp [block113ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5650 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 113 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block113_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5650 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5650 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5650) (width := 50) (hbound := by omega)
      (expected := block113ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block113_eq_chunked)
      (hzeroCandidates := block113ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
