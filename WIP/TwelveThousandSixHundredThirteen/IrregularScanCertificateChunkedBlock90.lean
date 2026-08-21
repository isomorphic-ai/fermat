import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 90

This block covers scan coordinates `[4500, 4550)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4500, 4550)`. -/
def block90ExpectedResidues_chunked : List (ZMod 12613) :=
  [3577, 8099, 4348, 8990, 2118, 3805, 3193, 5594, 392, 4392,
    9372, 3579, 3787, 4726, 10596, 6199, 5535, 2724, 3370, 4985,
    3166, 1824, 7163, 2094, 5008, 12116, 3379, 2935, 10992, 5055,
    8281, 5411, 8529, 6751, 9205, 1833, 7335, 5597, 11793, 9248,
    11606, 8255, 1435, 8886, 1233, 12483, 609, 5829, 12242, 4313]

/-- The one batched computation certificate for block 90. -/
theorem scanBlockResidues_block90_eq_chunked :
    scanBlockResidues 4500 50 = block90ExpectedResidues_chunked := by
  decide

private theorem block90ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block90ExpectedResidues_chunked[i.val]'(by
        simp [block90ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4500 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 90 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block90_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4500 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4500 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4500) (width := 50) (hbound := by omega)
      (expected := block90ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block90_eq_chunked)
      (hzeroCandidates := block90ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
