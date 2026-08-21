import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 59

This block covers scan coordinates `[2950, 3000)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2950, 3000)`. -/
def block59ExpectedResidues_chunked : List (ZMod 12613) :=
  [7113, 7012, 12325, 3175, 8647, 990, 4967, 5250, 1922, 4496,
    5719, 9866, 1980, 12587, 3730, 4635, 12149, 9248, 5059, 5720,
    6391, 9544, 6729, 2675, 6713, 3144, 9206, 9546, 3095, 968,
    12399, 8047, 1521, 1255, 3023, 9251, 11555, 11020, 7812, 5913,
    7182, 1223, 8667, 6173, 6797, 11470, 3239, 1476, 10706, 816]

/-- The one batched computation certificate for block 59. -/
theorem scanBlockResidues_block59_eq_chunked :
    scanBlockResidues 2950 50 = block59ExpectedResidues_chunked := by
  decide

private theorem block59ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block59ExpectedResidues_chunked[i.val]'(by
        simp [block59ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2950 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 59 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block59_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2950 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2950 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2950) (width := 50) (hbound := by omega)
      (expected := block59ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block59_eq_chunked)
      (hzeroCandidates := block59ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
