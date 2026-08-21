import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 25

This block covers scan coordinates `[1250, 1300)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1250, 1300)`. -/
def block25ExpectedResidues_chunked : List (ZMod 12613) :=
  [12322, 9188, 615, 7991, 663, 917, 4495, 9236, 5685, 9687,
    11333, 8481, 9639, 7992, 4291, 9326, 5984, 7048, 3227, 2096,
    1214, 7267, 7961, 4417, 5828, 11762, 11233, 8406, 376, 5202,
    9754, 5268, 6900, 2667, 833, 7074, 6211, 3369, 10281, 1381,
    6278, 8045, 2654, 1643, 10482, 6382, 7478, 8579, 2638, 1228]

/-- The one batched computation certificate for block 25. -/
theorem scanBlockResidues_block25_eq_chunked :
    scanBlockResidues 1250 50 = block25ExpectedResidues_chunked := by
  decide

private theorem block25ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block25ExpectedResidues_chunked[i.val]'(by
        simp [block25ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1250 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 25 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block25_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1250 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1250 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1250) (width := 50) (hbound := by omega)
      (expected := block25ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block25_eq_chunked)
      (hzeroCandidates := block25ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
