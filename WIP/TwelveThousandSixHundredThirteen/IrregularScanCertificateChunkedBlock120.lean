import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 120

This block covers scan coordinates `[6000, 6050)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[6000, 6050)`. -/
def block120ExpectedResidues_chunked : List (ZMod 12613) :=
  [8192, 11404, 1811, 1391, 9795, 11372, 193, 8425, 1681, 10792,
    7891, 6071, 6143, 1722, 410, 4840, 4337, 10149, 10535, 2717,
    5916, 11814, 4522, 155, 10227, 5594, 2394, 7624, 9996, 10360,
    1446, 11266, 9450, 3601, 5751, 3482, 5131, 4208, 8192, 4136,
    4337, 2925, 3189, 7865, 4677, 47, 7000, 6099, 2182, 3463]

/-- The one batched computation certificate for block 120. -/
theorem scanBlockResidues_block120_eq_chunked :
    scanBlockResidues 6000 50 = block120ExpectedResidues_chunked := by
  decide

private theorem block120ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block120ExpectedResidues_chunked[i.val]'(by
        simp [block120ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 6000 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 120 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block120_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 6000 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 6000 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 6000) (width := 50) (hbound := by omega)
      (expected := block120ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block120_eq_chunked)
      (hzeroCandidates := block120ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
