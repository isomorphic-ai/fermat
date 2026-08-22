import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 121

This block covers scan coordinates `[6050, 6100)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[6050, 6100)`. -/
def block121ExpectedResidues_chunked : List (ZMod 12613) :=
  [4999, 5454, 1458, 6640, 2939, 12455, 6857, 5407, 3293, 4570,
    8057, 3862, 9252, 8067, 4642, 305, 10809, 6281, 2029, 8548,
    10932, 3583, 4055, 11192, 6862, 10352, 2332, 6422, 3695, 1792,
    1085, 6713, 2140, 1334, 5948, 5792, 5087, 11116, 3523, 12487,
    10714, 7728, 9597, 647, 17, 221, 9661, 9005, 2996, 6971]

/-- The one batched computation certificate for block 121. -/
theorem scanBlockResidues_block121_eq_chunked :
    scanBlockResidues 6050 50 = block121ExpectedResidues_chunked := by
  decide

private theorem block121ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block121ExpectedResidues_chunked[i.val]'(by
        simp [block121ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 6050 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 121 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block121_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 6050 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 6050 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 6050) (width := 50) (hbound := by omega)
      (expected := block121ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block121_eq_chunked)
      (hzeroCandidates := block121ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
