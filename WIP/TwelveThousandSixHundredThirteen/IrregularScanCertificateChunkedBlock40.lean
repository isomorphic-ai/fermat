import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 40

This block covers scan coordinates `[2000, 2050)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2000, 2050)`. -/
def block40ExpectedResidues_chunked : List (ZMod 12613) :=
  [10910, 12325, 4675, 6704, 8939, 10742, 11102, 4528, 1698, 4241,
    11382, 12582, 9414, 10064, 2502, 8913, 1310, 344, 4328, 5006,
    1965, 12091, 8239, 11942, 4771, 514, 12208, 4558, 11100, 3293,
    7168, 7598, 8332, 3664, 5762, 2349, 1350, 2529, 10608, 3746,
    5158, 872, 9552, 11295, 10839, 5739, 10592, 488, 6175, 12399]

/-- The one batched computation certificate for block 40. -/
theorem scanBlockResidues_block40_eq_chunked :
    scanBlockResidues 2000 50 = block40ExpectedResidues_chunked := by
  decide

private theorem block40ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block40ExpectedResidues_chunked[i.val]'(by
        simp [block40ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2000 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 40 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block40_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2000 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2000 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2000) (width := 50) (hbound := by omega)
      (expected := block40ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block40_eq_chunked)
      (hzeroCandidates := block40ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
