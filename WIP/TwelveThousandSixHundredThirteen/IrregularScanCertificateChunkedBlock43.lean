import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 43

This block covers scan coordinates `[2150, 2200)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2150, 2200)`. -/
def block43ExpectedResidues_chunked : List (ZMod 12613) :=
  [4848, 576, 921, 6131, 8142, 12205, 8273, 7101, 11310, 6277,
    8177, 3026, 11496, 6697, 990, 10869, 10265, 2706, 6767, 6110,
    4767, 8837, 9150, 4845, 3928, 8573, 6876, 3112, 5316, 7019,
    5309, 10102, 597, 10352, 3529, 12129, 9322, 10669, 5266, 6233,
    8318, 758, 8276, 3157, 2255, 5675, 12177, 6027, 5496, 11908]

/-- The one batched computation certificate for block 43. -/
theorem scanBlockResidues_block43_eq_chunked :
    scanBlockResidues 2150 50 = block43ExpectedResidues_chunked := by
  decide

private theorem block43ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block43ExpectedResidues_chunked[i.val]'(by
        simp [block43ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2150 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 43 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block43_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2150 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2150 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2150) (width := 50) (hbound := by omega)
      (expected := block43ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block43_eq_chunked)
      (hzeroCandidates := block43ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
