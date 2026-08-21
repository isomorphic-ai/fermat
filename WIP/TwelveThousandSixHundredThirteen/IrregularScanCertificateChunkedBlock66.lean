import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 66

This block covers scan coordinates `[3300, 3350)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3300, 3350)`. -/
def block66ExpectedResidues_chunked : List (ZMod 12613) :=
  [2132, 10319, 1736, 5548, 3214, 4267, 6793, 3542, 5273, 357,
    1504, 8229, 9624, 6482, 11945, 10597, 10012, 401, 9105, 10478,
    3428, 8382, 3944, 1900, 8172, 9761, 9895, 11959, 10881, 6675,
    5023, 10131, 11677, 716, 11262, 6710, 874, 9032, 5414, 5810,
    10049, 12481, 5194, 10173, 8220, 6657, 9340, 2489, 11210, 10940]

/-- The one batched computation certificate for block 66. -/
theorem scanBlockResidues_block66_eq_chunked :
    scanBlockResidues 3300 50 = block66ExpectedResidues_chunked := by
  decide

private theorem block66ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block66ExpectedResidues_chunked[i.val]'(by
        simp [block66ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3300 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 66 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block66_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3300 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3300 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3300) (width := 50) (hbound := by omega)
      (expected := block66ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block66_eq_chunked)
      (hzeroCandidates := block66ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
