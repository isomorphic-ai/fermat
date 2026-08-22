import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 96

This block covers scan coordinates `[4800, 4850)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4800, 4850)`. -/
def block96ExpectedResidues_chunked : List (ZMod 12613) :=
  [11893, 8499, 2992, 7185, 10117, 6264, 11753, 10191, 3393, 684,
    2625, 4499, 7569, 8414, 8699, 6694, 6780, 9490, 10774, 2083,
    4231, 2565, 2857, 6526, 11743, 6191, 12173, 283, 12232, 3919,
    245, 11545, 5106, 12251, 8638, 10703, 2401, 5625, 1506, 11471,
    1953, 1104, 10290, 2031, 3876, 6363, 700, 8797, 5981, 5305]

/-- The one batched computation certificate for block 96. -/
theorem scanBlockResidues_block96_eq_chunked :
    scanBlockResidues 4800 50 = block96ExpectedResidues_chunked := by
  decide

private theorem block96ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block96ExpectedResidues_chunked[i.val]'(by
        simp [block96ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4800 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 96 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block96_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4800 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4800 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4800) (width := 50) (hbound := by omega)
      (expected := block96ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block96_eq_chunked)
      (hzeroCandidates := block96ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
