import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 41

This block covers scan coordinates `[2050, 2100)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2050, 2100)`. -/
def block41ExpectedResidues_chunked : List (ZMod 12613) :=
  [6216, 11083, 7753, 5156, 8619, 10040, 6087, 7638, 848, 10895,
    8041, 2850, 3731, 3408, 2999, 12466, 6036, 12554, 736, 4898,
    12465, 6553, 2141, 8643, 659, 4186, 5468, 11473, 9111, 10492,
    10869, 10471, 688, 1506, 9967, 4301, 12124, 3007, 8528, 1432,
    10747, 9588, 3507, 10326, 12125, 8399, 12365, 8951, 1766, 9011]

/-- The one batched computation certificate for block 41. -/
theorem scanBlockResidues_block41_eq_chunked :
    scanBlockResidues 2050 50 = block41ExpectedResidues_chunked := by
  decide

private theorem block41ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block41ExpectedResidues_chunked[i.val]'(by
        simp [block41ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2050 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 41 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block41_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2050 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2050 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2050) (width := 50) (hbound := by omega)
      (expected := block41ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block41_eq_chunked)
      (hzeroCandidates := block41ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
