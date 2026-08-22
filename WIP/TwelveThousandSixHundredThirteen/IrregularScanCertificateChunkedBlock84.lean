import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 84

This block covers scan coordinates `[4200, 4250)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4200, 4250)`. -/
def block84ExpectedResidues_chunked : List (ZMod 12613) :=
  [7420, 10934, 3368, 9899, 291, 2766, 6166, 2243, 789, 1440,
    6745, 7510, 9182, 9984, 8503, 7664, 4960, 8064, 8023, 7341,
    1931, 3340, 5944, 11137, 1609, 8440, 2471, 2782, 12521, 7348,
    11436, 2460, 9372, 6662, 7257, 10094, 2996, 7977, 7906, 6780,
    3150, 2918, 3529, 5540, 10771, 5857, 10307, 6867, 9111, 2385]

/-- The one batched computation certificate for block 84. -/
theorem scanBlockResidues_block84_eq_chunked :
    scanBlockResidues 4200 50 = block84ExpectedResidues_chunked := by
  decide

private theorem block84ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block84ExpectedResidues_chunked[i.val]'(by
        simp [block84ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4200 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 84 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block84_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4200 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4200 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4200) (width := 50) (hbound := by omega)
      (expected := block84ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block84_eq_chunked)
      (hzeroCandidates := block84ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
