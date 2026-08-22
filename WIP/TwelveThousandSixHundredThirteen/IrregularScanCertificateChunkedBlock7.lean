import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 7

This block covers scan coordinates `[350, 400)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[350, 400)`. -/
def block7ExpectedResidues_chunked : List (ZMod 12613) :=
  [6695, 9408, 3518, 2907, 11463, 635, 4859, 2907, 7391, 2616,
    3522, 2363, 12549, 10518, 6586, 534, 5268, 6042, 11976, 8210,
    9607, 10438, 3782, 7021, 8277, 9313, 4686, 7442, 1836, 8089,
    1347, 1072, 1703, 6873, 11277, 12057, 2688, 3383, 10505, 3663,
    5480, 3051, 11938, 11755, 6327, 9023, 392, 10436, 12328, 11964]

/-- The one batched computation certificate for block 7. -/
theorem scanBlockResidues_block7_eq_chunked :
    scanBlockResidues 350 50 = block7ExpectedResidues_chunked := by
  decide

private theorem block7ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block7ExpectedResidues_chunked[i.val]'(by
        simp [block7ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 350 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 7 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block7_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 350 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 350 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 350) (width := 50) (hbound := by omega)
      (expected := block7ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block7_eq_chunked)
      (hzeroCandidates := block7ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
