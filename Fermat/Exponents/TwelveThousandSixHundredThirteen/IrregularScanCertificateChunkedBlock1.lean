import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 1

This block covers scan coordinates `[50, 100)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[50, 100)`. -/
def block1ExpectedResidues_chunked : List (ZMod 12613) :=
  [11912, 1505, 2811, 4000, 600, 11963, 11374, 11287, 11400, 12163,
    10585, 11786, 10299, 4057, 10369, 6527, 338, 6978, 3472, 1549,
    2707, 12502, 475, 353, 4639, 3038, 1050, 1916, 7080, 6210,
    11966, 8782, 12534, 5468, 3674, 7242, 11736, 5537, 5425, 153,
    5729, 7568, 12594, 1328, 6817, 11365, 1835, 3948, 9571, 8472]

/-- The one batched computation certificate for block 1. -/
theorem scanBlockResidues_block1_eq_chunked :
    scanBlockResidues 50 50 = block1ExpectedResidues_chunked := by
  decide

private theorem block1ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block1ExpectedResidues_chunked[i.val]'(by
        simp [block1ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 50 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 1 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block1_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 50 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 50 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 50) (width := 50) (hbound := by omega)
      (expected := block1ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block1_eq_chunked)
      (hzeroCandidates := block1ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
