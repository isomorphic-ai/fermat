import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 58

This block covers scan coordinates `[2900, 2950)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2900, 2950)`. -/
def block58ExpectedResidues_chunked : List (ZMod 12613) :=
  [3659, 8311, 10415, 1770, 11783, 9390, 10103, 4895, 3833, 10987,
    2484, 7772, 10666, 4918, 12546, 5730, 4916, 4243, 7227, 6585,
    5981, 6898, 9672, 6178, 2390, 8034, 5194, 3961, 8297, 8254,
    2653, 4172, 8189, 6295, 2401, 6234, 7695, 7683, 1793, 3195,
    7368, 9605, 9537, 2093, 9806, 2166, 5633, 11879, 6316, 10684]

/-- The one batched computation certificate for block 58. -/
theorem scanBlockResidues_block58_eq_chunked :
    scanBlockResidues 2900 50 = block58ExpectedResidues_chunked := by
  decide

private theorem block58ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block58ExpectedResidues_chunked[i.val]'(by
        simp [block58ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2900 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 58 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block58_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2900 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2900 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2900) (width := 50) (hbound := by omega)
      (expected := block58ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block58_eq_chunked)
      (hzeroCandidates := block58ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
