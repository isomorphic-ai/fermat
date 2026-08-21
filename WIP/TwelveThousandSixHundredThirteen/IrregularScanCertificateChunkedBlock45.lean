import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 45

This block covers scan coordinates `[2250, 2300)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2250, 2300)`. -/
def block45ExpectedResidues_chunked : List (ZMod 12613) :=
  [5203, 2800, 9536, 9116, 8091, 6066, 5321, 9521, 6505, 11131,
    4994, 631, 1879, 10226, 2570, 5159, 12302, 2203, 1128, 11049,
    2625, 1218, 3551, 10347, 618, 3169, 7747, 7952, 4496, 4438,
    10677, 1313, 1213, 2187, 2880, 6685, 7994, 10093, 10501, 7783,
    10910, 4745, 8819, 9712, 5873, 10787, 9285, 3018, 9244, 10827]

/-- The one batched computation certificate for block 45. -/
theorem scanBlockResidues_block45_eq_chunked :
    scanBlockResidues 2250 50 = block45ExpectedResidues_chunked := by
  decide

private theorem block45ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block45ExpectedResidues_chunked[i.val]'(by
        simp [block45ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2250 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 45 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block45_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2250 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2250 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2250) (width := 50) (hbound := by omega)
      (expected := block45ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block45_eq_chunked)
      (hzeroCandidates := block45ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
