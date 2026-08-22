import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 99

This block covers scan coordinates `[4950, 5000)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4950, 5000)`. -/
def block99ExpectedResidues_chunked : List (ZMod 12613) :=
  [7965, 7931, 7769, 10294, 4342, 1477, 4875, 1027, 2262, 7228,
    2483, 5045, 10472, 9761, 11320, 3893, 8485, 7831, 1484, 4329,
    3228, 3663, 10715, 4271, 8642, 5806, 1044, 1150, 7312, 516,
    3272, 9633, 2069, 4786, 2499, 1463, 532, 10300, 2901, 3315,
    8344, 4537, 3776, 5095, 2491, 9269, 4832, 11901, 59, 1292]

/-- The one batched computation certificate for block 99. -/
theorem scanBlockResidues_block99_eq_chunked :
    scanBlockResidues 4950 50 = block99ExpectedResidues_chunked := by
  decide

private theorem block99ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block99ExpectedResidues_chunked[i.val]'(by
        simp [block99ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4950 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 99 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block99_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4950 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4950 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4950) (width := 50) (hbound := by omega)
      (expected := block99ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block99_eq_chunked)
      (hzeroCandidates := block99ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
