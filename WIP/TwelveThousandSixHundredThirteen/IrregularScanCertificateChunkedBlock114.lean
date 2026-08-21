import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 114

This block covers scan coordinates `[5700, 5750)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5700, 5750)`. -/
def block114ExpectedResidues_chunked : List (ZMod 12613) :=
  [5773, 7570, 6626, 463, 2592, 10799, 8696, 2309, 8547, 2205,
    7761, 2297, 3079, 3487, 6191, 11662, 7975, 6471, 23, 1359,
    4571, 1209, 8765, 9236, 9164, 5867, 2644, 2955, 1941, 5575,
    2321, 10281, 10204, 7332, 6857, 3710, 9660, 8566, 5774, 963,
    12473, 10121, 9342, 4250, 11726, 7191, 6693, 9267, 7894, 11718]

/-- The one batched computation certificate for block 114. -/
theorem scanBlockResidues_block114_eq_chunked :
    scanBlockResidues 5700 50 = block114ExpectedResidues_chunked := by
  decide

private theorem block114ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block114ExpectedResidues_chunked[i.val]'(by
        simp [block114ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5700 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 114 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block114_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5700 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5700 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5700) (width := 50) (hbound := by omega)
      (expected := block114ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block114_eq_chunked)
      (hzeroCandidates := block114ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
