import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 117

This block covers scan coordinates `[5850, 5900)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5850, 5900)`. -/
def block117ExpectedResidues_chunked : List (ZMod 12613) :=
  [1352, 229, 9929, 9676, 2206, 11906, 4734, 2827, 5055, 2946,
    5311, 10353, 5101, 7832, 1715, 144, 2418, 6969, 551, 6960,
    9918, 11251, 9916, 2833, 9048, 1718, 1497, 4551, 4715, 2633,
    1022, 8290, 6970, 8605, 12480, 590, 8516, 1805, 3539, 10300,
    7155, 7781, 7602, 5805, 3651, 2067, 1219, 173, 4201, 8388]

/-- The one batched computation certificate for block 117. -/
theorem scanBlockResidues_block117_eq_chunked :
    scanBlockResidues 5850 50 = block117ExpectedResidues_chunked := by
  decide

private theorem block117ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block117ExpectedResidues_chunked[i.val]'(by
        simp [block117ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5850 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 117 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block117_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5850 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5850 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5850) (width := 50) (hbound := by omega)
      (expected := block117ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block117_eq_chunked)
      (hzeroCandidates := block117ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
