import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 85

This block covers scan coordinates `[4250, 4300)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4250, 4300)`. -/
def block85ExpectedResidues_chunked : List (ZMod 12613) :=
  [5777, 8418, 7910, 1952, 2377, 5782, 1687, 4300, 8601, 2159,
    9545, 283, 2480, 5198, 4839, 6577, 11711, 5469, 7843, 5199,
    10036, 287, 6707, 8503, 127, 9610, 5625, 6275, 7071, 1999,
    7577, 12009, 541, 2208, 12087, 12126, 8525, 1638, 6864, 4034,
    6778, 4960, 6495, 12076, 9807, 7757, 8030, 724, 4775, 11045]

/-- The one batched computation certificate for block 85. -/
theorem scanBlockResidues_block85_eq_chunked :
    scanBlockResidues 4250 50 = block85ExpectedResidues_chunked := by
  decide

private theorem block85ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block85ExpectedResidues_chunked[i.val]'(by
        simp [block85ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4250 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 85 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block85_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4250 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4250 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4250) (width := 50) (hbound := by omega)
      (expected := block85ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block85_eq_chunked)
      (hzeroCandidates := block85ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
