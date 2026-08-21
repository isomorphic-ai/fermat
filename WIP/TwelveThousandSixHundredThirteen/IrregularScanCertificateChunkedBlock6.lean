import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 6

This block covers scan coordinates `[300, 350)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[300, 350)`. -/
def block6ExpectedResidues_chunked : List (ZMod 12613) :=
  [7159, 6037, 5969, 12579, 8670, 3900, 8927, 10880, 6609, 3862,
    6285, 171, 4624, 8804, 4109, 4112, 11097, 3672, 5619, 780,
    6369, 9074, 9733, 217, 4144, 11224, 10457, 722, 10283, 12532,
    4804, 10873, 242, 6080, 9957, 9636, 8992, 11608, 9308, 6786,
    423, 7754, 2169, 9017, 5015, 11916, 4973, 3019, 67, 9047]

/-- The one batched computation certificate for block 6. -/
theorem scanBlockResidues_block6_eq_chunked :
    scanBlockResidues 300 50 = block6ExpectedResidues_chunked := by
  decide

private theorem block6ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block6ExpectedResidues_chunked[i.val]'(by
        simp [block6ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 300 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 6 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block6_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 300 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 300 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 300) (width := 50) (hbound := by omega)
      (expected := block6ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block6_eq_chunked)
      (hzeroCandidates := block6ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
