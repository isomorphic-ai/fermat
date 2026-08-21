import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 105

This block covers scan coordinates `[5250, 5300)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5250, 5300)`. -/
def block105ExpectedResidues_chunked : List (ZMod 12613) :=
  [9255, 2996, 5163, 1364, 7648, 4533, 9863, 8119, 4658, 3195,
    2281, 12245, 7714, 11382, 6063, 6604, 2891, 0, 7778, 11160,
    11458, 3559, 5465, 9955, 3062, 3369, 1479, 6954, 1977, 9574,
    8273, 404, 1127, 3386, 5127, 7788, 10622, 10038, 1869, 10855,
    4277, 5661, 3240, 1510, 5555, 3044, 7810, 12609, 10859, 6370]

/-- The one batched computation certificate for block 105. -/
theorem scanBlockResidues_block105_eq_chunked :
    scanBlockResidues 5250 50 = block105ExpectedResidues_chunked := by
  decide

private theorem block105ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block105ExpectedResidues_chunked[i.val]'(by
        simp [block105ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5250 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 105 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block105_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5250 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5250 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5250) (width := 50) (hbound := by omega)
      (expected := block105ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block105_eq_chunked)
      (hzeroCandidates := block105ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
