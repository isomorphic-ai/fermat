import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 26

This block covers scan coordinates `[1300, 1350)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1300, 1350)`. -/
def block26ExpectedResidues_chunked : List (ZMod 12613) :=
  [1466, 7303, 766, 6607, 9756, 5879, 7526, 1674, 11748, 11185,
    10642, 7468, 934, 1389, 6826, 9475, 1835, 9299, 9934, 5433,
    2372, 1018, 10967, 2454, 11765, 11867, 4116, 1976, 7278, 8276,
    919, 12021, 3065, 8420, 4220, 685, 6831, 4506, 10407, 3568,
    9394, 1566, 10080, 6830, 907, 4702, 9261, 4524, 1369, 12217]

/-- The one batched computation certificate for block 26. -/
theorem scanBlockResidues_block26_eq_chunked :
    scanBlockResidues 1300 50 = block26ExpectedResidues_chunked := by
  decide

private theorem block26ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block26ExpectedResidues_chunked[i.val]'(by
        simp [block26ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1300 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 26 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block26_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1300 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1300 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1300) (width := 50) (hbound := by omega)
      (expected := block26ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block26_eq_chunked)
      (hzeroCandidates := block26ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
