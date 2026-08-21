import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 39

This block covers scan coordinates `[1950, 2000)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1950, 2000)`. -/
def block39ExpectedResidues_chunked : List (ZMod 12613) :=
  [10255, 7073, 4418, 9403, 1934, 11909, 8620, 240, 6358, 6686,
    9322, 2072, 7109, 4719, 6781, 9698, 12294, 10838, 7288, 4276,
    2762, 3875, 1951, 7289, 8719, 10559, 10850, 11147, 2527, 12514,
    9938, 12060, 7678, 873, 1255, 4353, 4442, 9474, 8300, 5991,
    3391, 11970, 8626, 3791, 5800, 1677, 6987, 1807, 685, 7548]

/-- The one batched computation certificate for block 39. -/
theorem scanBlockResidues_block39_eq_chunked :
    scanBlockResidues 1950 50 = block39ExpectedResidues_chunked := by
  decide

private theorem block39ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block39ExpectedResidues_chunked[i.val]'(by
        simp [block39ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1950 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 39 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block39_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1950 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1950 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1950) (width := 50) (hbound := by omega)
      (expected := block39ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block39_eq_chunked)
      (hzeroCandidates := block39ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
