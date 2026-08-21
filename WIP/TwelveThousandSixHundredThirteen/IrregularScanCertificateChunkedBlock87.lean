import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 87

This block covers scan coordinates `[4350, 4400)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4350, 4400)`. -/
def block87ExpectedResidues_chunked : List (ZMod 12613) :=
  [11839, 9190, 5987, 2964, 1621, 10045, 6594, 320, 6710, 9427,
    8698, 6129, 2108, 2948, 5450, 4689, 10795, 11173, 3319, 40,
    10361, 2839, 9312, 5972, 428, 8041, 10947, 8635, 9623, 9064,
    6987, 7733, 12274, 1881, 6407, 8466, 9728, 7039, 5855, 3533,
    12587, 5488, 8155, 11122, 702, 3175, 7652, 8803, 10501, 11890]

/-- The one batched computation certificate for block 87. -/
theorem scanBlockResidues_block87_eq_chunked :
    scanBlockResidues 4350 50 = block87ExpectedResidues_chunked := by
  decide

private theorem block87ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block87ExpectedResidues_chunked[i.val]'(by
        simp [block87ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4350 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 87 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block87_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4350 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4350 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4350) (width := 50) (hbound := by omega)
      (expected := block87ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block87_eq_chunked)
      (hzeroCandidates := block87ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
