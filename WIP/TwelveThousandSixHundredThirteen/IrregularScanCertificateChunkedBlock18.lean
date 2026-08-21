import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 18

This block covers scan coordinates `[900, 950)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[900, 950)`. -/
def block18ExpectedResidues_chunked : List (ZMod 12613) :=
  [12318, 5030, 6052, 3614, 10768, 9408, 7837, 5724, 4797, 5729,
    2450, 10047, 6966, 5477, 3055, 8425, 4595, 9770, 9774, 11042,
    9974, 9610, 7730, 5164, 4198, 4083, 6078, 10049, 1425, 5003,
    5880, 6079, 7891, 5912, 11796, 8665, 3077, 6445, 1488, 8356,
    2646, 10703, 2125, 3770, 6525, 9080, 9004, 11448, 1784, 10441]

/-- The one batched computation certificate for block 18. -/
theorem scanBlockResidues_block18_eq_chunked :
    scanBlockResidues 900 50 = block18ExpectedResidues_chunked := by
  decide

private theorem block18ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block18ExpectedResidues_chunked[i.val]'(by
        simp [block18ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 900 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 18 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block18_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 900 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 900 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 900) (width := 50) (hbound := by omega)
      (expected := block18ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block18_eq_chunked)
      (hzeroCandidates := block18ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
