import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 108

This block covers scan coordinates `[5400, 5450)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5400, 5450)`. -/
def block108ExpectedResidues_chunked : List (ZMod 12613) :=
  [10383, 9576, 10563, 7172, 2584, 519, 10875, 12160, 4133, 10111,
    11959, 687, 9226, 5982, 7336, 9440, 12376, 5783, 5933, 6280,
    1399, 781, 2347, 4569, 4794, 2979, 2719, 8963, 9695, 2130,
    8570, 2867, 12417, 5494, 5804, 11540, 3760, 11432, 10866, 3704,
    8622, 5171, 1459, 3079, 9438, 3006, 9578, 11887, 778, 4830]

/-- The one batched computation certificate for block 108. -/
theorem scanBlockResidues_block108_eq_chunked :
    scanBlockResidues 5400 50 = block108ExpectedResidues_chunked := by
  decide

private theorem block108ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block108ExpectedResidues_chunked[i.val]'(by
        simp [block108ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5400 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 108 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block108_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5400 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5400 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5400) (width := 50) (hbound := by omega)
      (expected := block108ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block108_eq_chunked)
      (hzeroCandidates := block108ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
