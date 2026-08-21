import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 86

This block covers scan coordinates `[4300, 4350)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4300, 4350)`. -/
def block86ExpectedResidues_chunked : List (ZMod 12613) :=
  [38, 8185, 4764, 11673, 12197, 9063, 3001, 1501, 12524, 4256,
    12265, 2294, 769, 10520, 12532, 9094, 7866, 5118, 3772, 2229,
    10045, 7934, 10614, 8650, 1180, 8692, 8571, 2662, 7062, 8900,
    4552, 6249, 5572, 3352, 4535, 4799, 9398, 12485, 848, 28,
    10079, 9047, 10648, 6185, 2286, 8125, 11262, 1693, 3453, 3300]

/-- The one batched computation certificate for block 86. -/
theorem scanBlockResidues_block86_eq_chunked :
    scanBlockResidues 4300 50 = block86ExpectedResidues_chunked := by
  decide

private theorem block86ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block86ExpectedResidues_chunked[i.val]'(by
        simp [block86ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4300 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 86 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block86_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4300 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4300 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4300) (width := 50) (hbound := by omega)
      (expected := block86ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block86_eq_chunked)
      (hzeroCandidates := block86ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
