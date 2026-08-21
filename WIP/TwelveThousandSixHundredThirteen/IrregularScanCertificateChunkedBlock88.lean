import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 88

This block covers scan coordinates `[4400, 4450)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4400, 4450)`. -/
def block88ExpectedResidues_chunked : List (ZMod 12613) :=
  [1708, 3566, 2543, 7446, 10020, 3007, 5657, 1903, 5703, 9526,
    7595, 8521, 7243, 10121, 11982, 716, 6382, 9395, 6163, 9929,
    8498, 1106, 6176, 4366, 10214, 1851, 277, 11532, 3025, 4920,
    3787, 9422, 1220, 8798, 6751, 8617, 10822, 2967, 8, 9347,
    6682, 7534, 2550, 1615, 2403, 5367, 3651, 8642, 8626, 4434]

/-- The one batched computation certificate for block 88. -/
theorem scanBlockResidues_block88_eq_chunked :
    scanBlockResidues 4400 50 = block88ExpectedResidues_chunked := by
  decide

private theorem block88ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block88ExpectedResidues_chunked[i.val]'(by
        simp [block88ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4400 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 88 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block88_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4400 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4400 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4400) (width := 50) (hbound := by omega)
      (expected := block88ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block88_eq_chunked)
      (hzeroCandidates := block88ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
