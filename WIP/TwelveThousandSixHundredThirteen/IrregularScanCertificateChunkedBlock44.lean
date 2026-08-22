import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 44

This block covers scan coordinates `[2200, 2250)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2200, 2250)`. -/
def block44ExpectedResidues_chunked : List (ZMod 12613) :=
  [3678, 1068, 173, 9207, 3939, 1073, 10175, 11488, 12117, 5338,
    2172, 4188, 1432, 6012, 6433, 7405, 8752, 8461, 3637, 3518,
    9677, 1429, 9835, 4654, 4108, 398, 11204, 11428, 12499, 5111,
    956, 12011, 3084, 10002, 8974, 7419, 7506, 5737, 1298, 4054,
    3197, 11510, 10948, 8504, 6087, 10350, 11081, 7093, 5474, 2431]

/-- The one batched computation certificate for block 44. -/
theorem scanBlockResidues_block44_eq_chunked :
    scanBlockResidues 2200 50 = block44ExpectedResidues_chunked := by
  decide

private theorem block44ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block44ExpectedResidues_chunked[i.val]'(by
        simp [block44ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2200 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 44 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block44_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2200 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2200 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2200) (width := 50) (hbound := by omega)
      (expected := block44ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block44_eq_chunked)
      (hzeroCandidates := block44ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
