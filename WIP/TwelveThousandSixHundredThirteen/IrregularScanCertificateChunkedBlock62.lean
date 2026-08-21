import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 62

This block covers scan coordinates `[3100, 3150)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3100, 3150)`. -/
def block62ExpectedResidues_chunked : List (ZMod 12613) :=
  [12288, 749, 5468, 3106, 10985, 4486, 3637, 5504, 7995, 1659,
    10800, 5119, 3002, 5700, 9208, 9689, 1850, 6995, 9319, 5232,
    12138, 4183, 2941, 3739, 9605, 10465, 12593, 12569, 5611, 2962,
    567, 10596, 2850, 1232, 12500, 2243, 4693, 1299, 12396, 6561,
    11198, 4704, 3056, 8560, 10874, 9266, 12557, 5019, 1850, 456]

/-- The one batched computation certificate for block 62. -/
theorem scanBlockResidues_block62_eq_chunked :
    scanBlockResidues 3100 50 = block62ExpectedResidues_chunked := by
  decide

private theorem block62ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block62ExpectedResidues_chunked[i.val]'(by
        simp [block62ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3100 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 62 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block62_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3100 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3100 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3100) (width := 50) (hbound := by omega)
      (expected := block62ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block62_eq_chunked)
      (hzeroCandidates := block62ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
