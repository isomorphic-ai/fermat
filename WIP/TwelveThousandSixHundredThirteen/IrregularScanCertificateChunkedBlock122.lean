import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 122

This block covers scan coordinates `[6100, 6150)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[6100, 6150)`. -/
def block122ExpectedResidues_chunked : List (ZMod 12613) :=
  [3270, 6232, 9226, 10424, 10920, 6048, 11526, 7452, 11420, 1213,
    7331, 2347, 534, 8875, 4148, 10086, 9306, 8133, 7078, 2273,
    8633, 3007, 698, 1079, 10725, 1426, 6842, 1253, 5352, 7895,
    6146, 7268, 10399, 2831, 4816, 3553, 11677, 4584, 3889, 2788,
    9094, 3887, 12507, 1003, 11536, 12175, 7234, 7488, 7823, 11636]

/-- The one batched computation certificate for block 122. -/
theorem scanBlockResidues_block122_eq_chunked :
    scanBlockResidues 6100 50 = block122ExpectedResidues_chunked := by
  decide

private theorem block122ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block122ExpectedResidues_chunked[i.val]'(by
        simp [block122ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 6100 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 122 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block122_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 6100 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 6100 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 6100) (width := 50) (hbound := by omega)
      (expected := block122ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block122_eq_chunked)
      (hzeroCandidates := block122ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
