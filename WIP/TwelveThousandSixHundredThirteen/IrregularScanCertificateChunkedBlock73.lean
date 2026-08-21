import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 73

This block covers scan coordinates `[3650, 3700)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3650, 3700)`. -/
def block73ExpectedResidues_chunked : List (ZMod 12613) :=
  [306, 5626, 4649, 5402, 8743, 1254, 439, 1665, 6810, 430,
    5518, 2317, 5772, 9867, 1854, 8985, 4238, 11796, 1828, 9260,
    12532, 8489, 4393, 586, 1520, 4599, 1761, 472, 820, 7583,
    6571, 4426, 9863, 7404, 11631, 11896, 9585, 10837, 3215, 2142,
    10219, 8538, 11570, 5262, 2874, 11745, 12098, 63, 10225, 7373]

/-- The one batched computation certificate for block 73. -/
theorem scanBlockResidues_block73_eq_chunked :
    scanBlockResidues 3650 50 = block73ExpectedResidues_chunked := by
  decide

private theorem block73ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block73ExpectedResidues_chunked[i.val]'(by
        simp [block73ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3650 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 73 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block73_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3650 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3650 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3650) (width := 50) (hbound := by omega)
      (expected := block73ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block73_eq_chunked)
      (hzeroCandidates := block73ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
