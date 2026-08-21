import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 33

This block covers scan coordinates `[1650, 1700)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1650, 1700)`. -/
def block33ExpectedResidues_chunked : List (ZMod 12613) :=
  [5059, 8754, 8508, 781, 9448, 8613, 3056, 5489, 9922, 8564,
    7013, 9243, 3058, 6877, 4460, 9833, 7485, 3321, 9626, 3917,
    3490, 4470, 7322, 5051, 12449, 11435, 3623, 927, 7181, 1469,
    4416, 4893, 1379, 7224, 9295, 4002, 2721, 1844, 3834, 5144,
    4340, 3542, 1768, 9794, 7783, 6967, 452, 11500, 7202, 4792]

/-- The one batched computation certificate for block 33. -/
theorem scanBlockResidues_block33_eq_chunked :
    scanBlockResidues 1650 50 = block33ExpectedResidues_chunked := by
  decide

private theorem block33ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block33ExpectedResidues_chunked[i.val]'(by
        simp [block33ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1650 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 33 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block33_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1650 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1650 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1650) (width := 50) (hbound := by omega)
      (expected := block33ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block33_eq_chunked)
      (hzeroCandidates := block33ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
