import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 5

This block covers scan coordinates `[250, 300)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[250, 300)`. -/
def block5ExpectedResidues_chunked : List (ZMod 12613) :=
  [0, 8840, 8379, 3371, 4274, 6421, 7689, 8429, 6025, 3308,
    12164, 5465, 1480, 3389, 4361, 9165, 3416, 3859, 3936, 2690,
    9967, 7049, 11802, 8296, 12323, 3605, 1834, 6325, 2590, 12466,
    3642, 12314, 7212, 9779, 1979, 5497, 10198, 5758, 9689, 485,
    1159, 12129, 1161, 10180, 6377, 619, 10275, 7748, 4249, 10292]

/-- The one batched computation certificate for block 5. -/
theorem scanBlockResidues_block5_eq_chunked :
    scanBlockResidues 250 50 = block5ExpectedResidues_chunked := by
  decide

private theorem block5ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block5ExpectedResidues_chunked[i.val]'(by
        simp [block5ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 250 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 5 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block5_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 250 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 250 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 250) (width := 50) (hbound := by omega)
      (expected := block5ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block5_eq_chunked)
      (hzeroCandidates := block5ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
