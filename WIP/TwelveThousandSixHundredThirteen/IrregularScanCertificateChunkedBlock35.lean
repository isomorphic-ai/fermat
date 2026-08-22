import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 35

This block covers scan coordinates `[1750, 1800)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1750, 1800)`. -/
def block35ExpectedResidues_chunked : List (ZMod 12613) :=
  [5105, 2359, 8759, 1947, 9717, 12475, 1640, 1052, 3672, 6812,
    5065, 7056, 1881, 3864, 8900, 2294, 368, 867, 10591, 8667,
    8176, 2859, 8522, 5516, 10014, 3561, 1304, 209, 3023, 2226,
    8495, 2848, 7019, 4216, 7448, 3861, 4659, 6232, 608, 5621,
    11600, 11436, 4249, 8185, 6530, 9982, 7826, 7066, 10773, 7921]

/-- The one batched computation certificate for block 35. -/
theorem scanBlockResidues_block35_eq_chunked :
    scanBlockResidues 1750 50 = block35ExpectedResidues_chunked := by
  decide

private theorem block35ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block35ExpectedResidues_chunked[i.val]'(by
        simp [block35ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1750 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 35 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block35_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1750 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1750 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1750) (width := 50) (hbound := by omega)
      (expected := block35ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block35_eq_chunked)
      (hzeroCandidates := block35ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
