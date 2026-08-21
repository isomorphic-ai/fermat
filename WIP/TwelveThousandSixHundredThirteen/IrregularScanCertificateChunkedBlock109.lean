import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 109

This block covers scan coordinates `[5450, 5500)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5450, 5500)`. -/
def block109ExpectedResidues_chunked : List (ZMod 12613) :=
  [1715, 6572, 625, 4536, 1891, 5125, 9293, 12355, 3546, 12535,
    3084, 677, 11348, 7019, 780, 1986, 9570, 5479, 2727, 6642,
    3532, 3486, 4099, 8578, 28, 11379, 505, 3933, 7189, 12229,
    3047, 6866, 7025, 9362, 3575, 9294, 2363, 1401, 5186, 7788,
    11907, 5432, 6137, 12151, 6385, 10841, 12067, 4715, 12116, 11308]

/-- The one batched computation certificate for block 109. -/
theorem scanBlockResidues_block109_eq_chunked :
    scanBlockResidues 5450 50 = block109ExpectedResidues_chunked := by
  decide

private theorem block109ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block109ExpectedResidues_chunked[i.val]'(by
        simp [block109ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5450 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 109 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block109_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5450 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5450 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5450) (width := 50) (hbound := by omega)
      (expected := block109ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block109_eq_chunked)
      (hzeroCandidates := block109ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
