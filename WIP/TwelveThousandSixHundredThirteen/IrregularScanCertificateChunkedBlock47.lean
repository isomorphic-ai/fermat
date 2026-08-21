import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 47

This block covers scan coordinates `[2350, 2400)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2350, 2400)`. -/
def block47ExpectedResidues_chunked : List (ZMod 12613) :=
  [11284, 2805, 7594, 10920, 7518, 9653, 2050, 8204, 6246, 11588,
    6741, 7467, 7283, 7074, 5248, 7323, 6006, 3050, 1813, 12352,
    3653, 5601, 5958, 10704, 3995, 10586, 12545, 11146, 379, 8114,
    10048, 12115, 6557, 10701, 6183, 285, 10821, 5907, 3839, 2455,
    2832, 7296, 9647, 3473, 10030, 9380, 2921, 9883, 6425, 2318]

/-- The one batched computation certificate for block 47. -/
theorem scanBlockResidues_block47_eq_chunked :
    scanBlockResidues 2350 50 = block47ExpectedResidues_chunked := by
  decide

private theorem block47ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block47ExpectedResidues_chunked[i.val]'(by
        simp [block47ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2350 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 47 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block47_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2350 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2350 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2350) (width := 50) (hbound := by omega)
      (expected := block47ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block47_eq_chunked)
      (hzeroCandidates := block47ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
