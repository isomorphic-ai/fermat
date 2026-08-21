import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 46

This block covers scan coordinates `[2300, 2350)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2300, 2350)`. -/
def block46ExpectedResidues_chunked : List (ZMod 12613) :=
  [5989, 8697, 1242, 10678, 3980, 11439, 3806, 5516, 7062, 5707,
    6122, 1782, 5025, 11370, 3466, 12032, 5286, 417, 9727, 3753,
    11325, 5770, 4507, 9877, 6833, 5350, 8646, 4418, 10839, 11255,
    750, 726, 3616, 1850, 10653, 6393, 5399, 6449, 5158, 8834,
    6362, 9089, 11494, 11228, 11728, 6216, 2917, 4103, 11789, 7133]

/-- The one batched computation certificate for block 46. -/
theorem scanBlockResidues_block46_eq_chunked :
    scanBlockResidues 2300 50 = block46ExpectedResidues_chunked := by
  decide

private theorem block46ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block46ExpectedResidues_chunked[i.val]'(by
        simp [block46ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2300 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 46 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block46_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2300 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2300 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2300) (width := 50) (hbound := by omega)
      (expected := block46ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block46_eq_chunked)
      (hzeroCandidates := block46ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
