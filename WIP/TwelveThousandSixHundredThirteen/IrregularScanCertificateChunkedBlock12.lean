import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 12

This block covers scan coordinates `[600, 650)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[600, 650)`. -/
def block12ExpectedResidues_chunked : List (ZMod 12613) :=
  [11837, 6579, 2746, 1177, 3357, 2231, 11994, 3244, 1068, 8047,
    34, 11158, 1690, 12123, 311, 3119, 4524, 12338, 7734, 477,
    1491, 3968, 892, 3653, 10412, 11072, 7451, 4984, 6093, 2934,
    6088, 4911, 8040, 3256, 8435, 7126, 2655, 5556, 11704, 5772,
    8647, 9512, 3643, 11050, 8377, 12095, 5264, 3453, 2493, 8441]

/-- The one batched computation certificate for block 12. -/
theorem scanBlockResidues_block12_eq_chunked :
    scanBlockResidues 600 50 = block12ExpectedResidues_chunked := by
  decide

private theorem block12ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block12ExpectedResidues_chunked[i.val]'(by
        simp [block12ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 600 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 12 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block12_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 600 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 600 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 600) (width := 50) (hbound := by omega)
      (expected := block12ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block12_eq_chunked)
      (hzeroCandidates := block12ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
