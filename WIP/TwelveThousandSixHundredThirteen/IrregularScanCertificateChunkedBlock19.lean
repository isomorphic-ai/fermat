import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 19

This block covers scan coordinates `[950, 1000)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[950, 1000)`. -/
def block19ExpectedResidues_chunked : List (ZMod 12613) :=
  [11293, 1727, 788, 5324, 11358, 8559, 6617, 596, 10998, 5480,
    3644, 2406, 7212, 5409, 6411, 9449, 4915, 2211, 9609, 4822,
    12003, 9539, 340, 4759, 6928, 3181, 6197, 9593, 12556, 12136,
    9755, 8682, 2123, 5182, 1270, 11657, 8252, 6976, 11531, 9747,
    12312, 7840, 10344, 3783, 5826, 8603, 204, 12282, 7013, 6480]

/-- The one batched computation certificate for block 19. -/
theorem scanBlockResidues_block19_eq_chunked :
    scanBlockResidues 950 50 = block19ExpectedResidues_chunked := by
  decide

private theorem block19ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block19ExpectedResidues_chunked[i.val]'(by
        simp [block19ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 950 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 19 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block19_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 950 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 950 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 950) (width := 50) (hbound := by omega)
      (expected := block19ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block19_eq_chunked)
      (hzeroCandidates := block19ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
