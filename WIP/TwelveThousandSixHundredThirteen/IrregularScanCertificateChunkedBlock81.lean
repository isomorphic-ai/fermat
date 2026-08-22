import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 81

This block covers scan coordinates `[4050, 4100)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4050, 4100)`. -/
def block81ExpectedResidues_chunked : List (ZMod 12613) :=
  [4516, 1874, 5379, 4289, 1539, 11376, 684, 3257, 706, 6041,
    8781, 2394, 11540, 11410, 5575, 8986, 787, 4037, 5219, 6169,
    2059, 1629, 4195, 6602, 6954, 1069, 11153, 3254, 8535, 4161,
    3857, 4260, 4631, 5533, 2170, 1165, 7719, 5609, 7353, 6496,
    9380, 9226, 8871, 2632, 11696, 5777, 11921, 5062, 10792, 11321]

/-- The one batched computation certificate for block 81. -/
theorem scanBlockResidues_block81_eq_chunked :
    scanBlockResidues 4050 50 = block81ExpectedResidues_chunked := by
  decide

private theorem block81ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block81ExpectedResidues_chunked[i.val]'(by
        simp [block81ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4050 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 81 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block81_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4050 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4050 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4050) (width := 50) (hbound := by omega)
      (expected := block81ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block81_eq_chunked)
      (hzeroCandidates := block81ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
