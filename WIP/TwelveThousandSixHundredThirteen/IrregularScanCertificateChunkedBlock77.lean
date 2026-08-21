import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 77

This block covers scan coordinates `[3850, 3900)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3850, 3900)`. -/
def block77ExpectedResidues_chunked : List (ZMod 12613) :=
  [172, 6380, 4031, 4413, 10341, 8920, 7046, 6027, 11675, 5731,
    6145, 495, 3952, 10636, 6673, 10081, 6014, 7301, 9050, 7547,
    3609, 9959, 6134, 12592, 77, 7059, 8619, 4603, 11378, 130,
    1231, 6899, 9430, 4568, 5829, 9296, 11689, 5335, 11332, 7294,
    6491, 9625, 5421, 3142, 12530, 138, 7735, 10108, 7840, 6287]

/-- The one batched computation certificate for block 77. -/
theorem scanBlockResidues_block77_eq_chunked :
    scanBlockResidues 3850 50 = block77ExpectedResidues_chunked := by
  decide

private theorem block77ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block77ExpectedResidues_chunked[i.val]'(by
        simp [block77ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3850 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 77 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block77_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3850 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3850 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3850) (width := 50) (hbound := by omega)
      (expected := block77ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block77_eq_chunked)
      (hzeroCandidates := block77ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
