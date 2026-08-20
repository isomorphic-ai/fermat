import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 2

This block covers scan coordinates `[100, 150)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[100, 150)`. -/
def block2ExpectedResidues_chunked : List (ZMod 12613) :=
  [8453, 7911, 3, 9183, 5110, 2106, 1947, 9124, 8815, 5592,
    2960, 10310, 890, 433, 8679, 2152, 6073, 689, 11288, 8989,
    3549, 6401, 6758, 7369, 12388, 11109, 9264, 10972, 9310, 28,
    6503, 1013, 6286, 6750, 4489, 3888, 2532, 3394, 11446, 10277,
    615, 11783, 4685, 9737, 2761, 6982, 12135, 2689, 7220, 1971]

/-- The one batched computation certificate for block 2. -/
theorem scanBlockResidues_block2_eq_chunked :
    scanBlockResidues 100 50 = block2ExpectedResidues_chunked := by
  decide

private theorem block2ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block2ExpectedResidues_chunked[i.val]'(by
        simp [block2ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 100 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 2 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block2_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 100 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 100 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 100) (width := 50) (hbound := by omega)
      (expected := block2ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block2_eq_chunked)
      (hzeroCandidates := block2ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
