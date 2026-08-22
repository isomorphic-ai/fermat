import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 78

This block covers scan coordinates `[3900, 3950)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3900, 3950)`. -/
def block78ExpectedResidues_chunked : List (ZMod 12613) :=
  [8729, 12411, 6428, 12156, 1213, 6904, 7680, 6954, 10017, 9701,
    7587, 10380, 447, 11559, 9377, 4149, 4644, 5601, 558, 4748,
    2094, 5330, 10339, 4120, 4488, 2928, 3798, 7501, 2709, 8198,
    7866, 9517, 9161, 2551, 12541, 11054, 29, 1124, 513, 8202,
    1307, 7522, 11326, 819, 4729, 9715, 509, 11874, 3254, 256]

/-- The one batched computation certificate for block 78. -/
theorem scanBlockResidues_block78_eq_chunked :
    scanBlockResidues 3900 50 = block78ExpectedResidues_chunked := by
  decide

private theorem block78ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block78ExpectedResidues_chunked[i.val]'(by
        simp [block78ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3900 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 78 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block78_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3900 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3900 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3900) (width := 50) (hbound := by omega)
      (expected := block78ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block78_eq_chunked)
      (hzeroCandidates := block78ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
