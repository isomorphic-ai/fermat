import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 72

This block covers scan coordinates `[3600, 3650)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3600, 3650)`. -/
def block72ExpectedResidues_chunked : List (ZMod 12613) :=
  [5843, 9786, 737, 11770, 9890, 5358, 3853, 11963, 6453, 7781,
    781, 4286, 3141, 1182, 345, 7442, 9511, 7545, 2536, 3914,
    8212, 5097, 5547, 5087, 341, 1329, 12304, 7438, 8851, 2906,
    3128, 278, 8187, 3050, 5864, 3229, 5385, 10206, 4632, 10823,
    6968, 3174, 5930, 10710, 4447, 600, 460, 8816, 9173, 7394]

/-- The one batched computation certificate for block 72. -/
theorem scanBlockResidues_block72_eq_chunked :
    scanBlockResidues 3600 50 = block72ExpectedResidues_chunked := by
  decide

private theorem block72ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block72ExpectedResidues_chunked[i.val]'(by
        simp [block72ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3600 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 72 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block72_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3600 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3600 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3600) (width := 50) (hbound := by omega)
      (expected := block72ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block72_eq_chunked)
      (hzeroCandidates := block72ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
