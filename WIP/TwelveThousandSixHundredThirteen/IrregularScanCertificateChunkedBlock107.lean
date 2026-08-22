import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 107

This block covers scan coordinates `[5350, 5400)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5350, 5400)`. -/
def block107ExpectedResidues_chunked : List (ZMod 12613) :=
  [58, 8280, 12098, 5134, 6809, 488, 4272, 27, 12406, 4381,
    7466, 7929, 3566, 11797, 2342, 6672, 47, 8090, 2563, 1035,
    7083, 3120, 3906, 6406, 5153, 10345, 1246, 8195, 6007, 8536,
    7687, 8038, 11645, 6303, 8373, 9795, 1832, 5809, 10745, 7883,
    8006, 11875, 4904, 12071, 7940, 12336, 4746, 4232, 11512, 1400]

/-- The one batched computation certificate for block 107. -/
theorem scanBlockResidues_block107_eq_chunked :
    scanBlockResidues 5350 50 = block107ExpectedResidues_chunked := by
  decide

private theorem block107ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block107ExpectedResidues_chunked[i.val]'(by
        simp [block107ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5350 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 107 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block107_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5350 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5350 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5350) (width := 50) (hbound := by omega)
      (expected := block107ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block107_eq_chunked)
      (hzeroCandidates := block107ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
