import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 10

This block covers scan coordinates `[500, 550)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[500, 550)`. -/
def block10ExpectedResidues_chunked : List (ZMod 12613) :=
  [9557, 3779, 11748, 2936, 11669, 5522, 11692, 4523, 1884, 2773,
    3895, 11071, 1462, 8862, 5425, 8450, 5042, 8216, 6039, 7284,
    3276, 6672, 2216, 3422, 3096, 8633, 1116, 4639, 7405, 2178,
    11680, 11474, 8983, 9566, 4717, 5634, 12017, 3103, 8655, 11494,
    12180, 5483, 8455, 6874, 6234, 800, 8795, 9634, 9470, 84]

/-- The one batched computation certificate for block 10. -/
theorem scanBlockResidues_block10_eq_chunked :
    scanBlockResidues 500 50 = block10ExpectedResidues_chunked := by
  decide

private theorem block10ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block10ExpectedResidues_chunked[i.val]'(by
        simp [block10ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 500 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 10 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block10_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 500 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 500 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 500) (width := 50) (hbound := by omega)
      (expected := block10ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block10_eq_chunked)
      (hzeroCandidates := block10ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
