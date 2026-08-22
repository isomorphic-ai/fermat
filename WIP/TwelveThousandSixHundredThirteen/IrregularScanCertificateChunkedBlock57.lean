import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 57

This block covers scan coordinates `[2850, 2900)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2850, 2900)`. -/
def block57ExpectedResidues_chunked : List (ZMod 12613) :=
  [2893, 10576, 4026, 8019, 2620, 5631, 12296, 2777, 5507, 4806,
    1003, 7803, 10347, 11630, 7570, 2673, 4065, 2078, 10408, 5639,
    2792, 2631, 7310, 12056, 8587, 7911, 8388, 3162, 7749, 6230,
    6236, 6732, 3370, 4476, 1019, 2252, 1401, 6545, 11838, 1351,
    8889, 8592, 3334, 964, 5136, 2478, 4873, 940, 7199, 3047]

/-- The one batched computation certificate for block 57. -/
theorem scanBlockResidues_block57_eq_chunked :
    scanBlockResidues 2850 50 = block57ExpectedResidues_chunked := by
  decide

private theorem block57ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block57ExpectedResidues_chunked[i.val]'(by
        simp [block57ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2850 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 57 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block57_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2850 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2850 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2850) (width := 50) (hbound := by omega)
      (expected := block57ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block57_eq_chunked)
      (hzeroCandidates := block57ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
