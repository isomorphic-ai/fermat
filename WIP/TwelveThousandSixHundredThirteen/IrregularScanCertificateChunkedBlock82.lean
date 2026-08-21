import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 82

This block covers scan coordinates `[4100, 4150)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4100, 4150)`. -/
def block82ExpectedResidues_chunked : List (ZMod 12613) :=
  [1677, 9071, 4508, 3746, 8303, 47, 5698, 8493, 2113, 59,
    4683, 12333, 8096, 10531, 1579, 2682, 11644, 2758, 11474, 7496,
    5269, 6469, 773, 2341, 12246, 9574, 4146, 11608, 8932, 11018,
    3725, 237, 1447, 483, 7998, 257, 2682, 6141, 4604, 12230,
    2791, 7310, 8989, 7154, 7889, 10287, 4509, 1015, 365, 3499]

/-- The one batched computation certificate for block 82. -/
theorem scanBlockResidues_block82_eq_chunked :
    scanBlockResidues 4100 50 = block82ExpectedResidues_chunked := by
  decide

private theorem block82ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block82ExpectedResidues_chunked[i.val]'(by
        simp [block82ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4100 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 82 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block82_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4100 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4100 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4100) (width := 50) (hbound := by omega)
      (expected := block82ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block82_eq_chunked)
      (hzeroCandidates := block82ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
