import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 48

This block covers scan coordinates `[2400, 2450)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2400, 2450)`. -/
def block48ExpectedResidues_chunked : List (ZMod 12613) :=
  [2496, 7279, 3131, 5046, 4968, 4314, 8534, 3840, 2659, 1378,
    12324, 6494, 12159, 10843, 11906, 4995, 11516, 2378, 4170, 2931,
    2078, 3343, 2251, 11151, 11408, 6530, 5435, 4642, 1804, 11287,
    11689, 2022, 3264, 10147, 5102, 479, 3376, 9067, 7171, 10196,
    4200, 3136, 4073, 12215, 5010, 5676, 11872, 11883, 7440, 7855]

/-- The one batched computation certificate for block 48. -/
theorem scanBlockResidues_block48_eq_chunked :
    scanBlockResidues 2400 50 = block48ExpectedResidues_chunked := by
  decide

private theorem block48ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block48ExpectedResidues_chunked[i.val]'(by
        simp [block48ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2400 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 48 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block48_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2400 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2400 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2400) (width := 50) (hbound := by omega)
      (expected := block48ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block48_eq_chunked)
      (hzeroCandidates := block48ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
