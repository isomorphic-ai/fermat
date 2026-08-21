import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 14

This block covers scan coordinates `[700, 750)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[700, 750)`. -/
def block14ExpectedResidues_chunked : List (ZMod 12613) :=
  [2081, 1684, 12114, 2369, 12501, 4444, 8973, 1357, 972, 10061,
    5608, 9644, 1053, 10387, 6759, 1881, 320, 11815, 10978, 10116,
    3328, 2766, 11192, 2571, 577, 5631, 10559, 7524, 12379, 7195,
    11980, 4941, 1397, 9128, 2512, 10362, 668, 2194, 12126, 10188,
    3028, 2336, 12163, 11064, 12104, 10677, 6000, 4290, 10069, 3350]

/-- The one batched computation certificate for block 14. -/
theorem scanBlockResidues_block14_eq_chunked :
    scanBlockResidues 700 50 = block14ExpectedResidues_chunked := by
  decide

private theorem block14ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block14ExpectedResidues_chunked[i.val]'(by
        simp [block14ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 700 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 14 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block14_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 700 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 700 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 700) (width := 50) (hbound := by omega)
      (expected := block14ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block14_eq_chunked)
      (hzeroCandidates := block14ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
