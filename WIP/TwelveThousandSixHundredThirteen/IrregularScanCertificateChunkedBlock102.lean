import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 102

This block covers scan coordinates `[5100, 5150)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5100, 5150)`. -/
def block102ExpectedResidues_chunked : List (ZMod 12613) :=
  [11600, 615, 10498, 8249, 10869, 8932, 3022, 10538, 3942, 9140,
    6736, 6977, 8406, 1784, 1653, 500, 3644, 9135, 3855, 4559,
    1885, 11782, 6368, 9693, 4830, 6136, 4878, 10248, 2571, 11782,
    9901, 284, 7557, 8791, 377, 11222, 53, 439, 4670, 10184,
    11882, 9808, 4933, 1191, 861, 10952, 5956, 1237, 3076, 10308]

/-- The one batched computation certificate for block 102. -/
theorem scanBlockResidues_block102_eq_chunked :
    scanBlockResidues 5100 50 = block102ExpectedResidues_chunked := by
  decide

private theorem block102ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block102ExpectedResidues_chunked[i.val]'(by
        simp [block102ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5100 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 102 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block102_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5100 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5100 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5100) (width := 50) (hbound := by omega)
      (expected := block102ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block102_eq_chunked)
      (hzeroCandidates := block102ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
