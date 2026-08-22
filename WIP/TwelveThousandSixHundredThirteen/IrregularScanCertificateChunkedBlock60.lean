import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 60

This block covers scan coordinates `[3000, 3050)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3000, 3050)`. -/
def block60ExpectedResidues_chunked : List (ZMod 12613) :=
  [9478, 11644, 269, 1313, 6536, 8695, 6814, 1401, 6006, 1566,
    2118, 2222, 8122, 3575, 6025, 2513, 7696, 11028, 4734, 8413,
    467, 4390, 1283, 5307, 8111, 5356, 9172, 5607, 8942, 10550,
    5554, 1783, 1992, 3882, 8725, 6885, 1687, 5975, 10362, 1899,
    2356, 8835, 4634, 5933, 1179, 7402, 6632, 7240, 10007, 3180]

/-- The one batched computation certificate for block 60. -/
theorem scanBlockResidues_block60_eq_chunked :
    scanBlockResidues 3000 50 = block60ExpectedResidues_chunked := by
  decide

private theorem block60ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block60ExpectedResidues_chunked[i.val]'(by
        simp [block60ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3000 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 60 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block60_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3000 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3000 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3000) (width := 50) (hbound := by omega)
      (expected := block60ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block60_eq_chunked)
      (hzeroCandidates := block60ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
