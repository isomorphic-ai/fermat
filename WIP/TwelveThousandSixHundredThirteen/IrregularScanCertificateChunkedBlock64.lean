import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 64

This block covers scan coordinates `[3200, 3250)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3200, 3250)`. -/
def block64ExpectedResidues_chunked : List (ZMod 12613) :=
  [6281, 6497, 9605, 3089, 3404, 3776, 6112, 1868, 11904, 5369,
    10645, 6282, 2325, 8184, 7603, 8317, 6590, 6406, 1710, 12413,
    8918, 2127, 11266, 8339, 7722, 11489, 7943, 346, 5293, 8296,
    8217, 12113, 6305, 3142, 7291, 9262, 10535, 126, 2716, 10842,
    1743, 3616, 8451, 620, 9607, 6073, 2551, 1809, 8307, 1398]

/-- The one batched computation certificate for block 64. -/
theorem scanBlockResidues_block64_eq_chunked :
    scanBlockResidues 3200 50 = block64ExpectedResidues_chunked := by
  decide

private theorem block64ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block64ExpectedResidues_chunked[i.val]'(by
        simp [block64ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3200 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 64 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block64_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3200 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3200 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3200) (width := 50) (hbound := by omega)
      (expected := block64ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block64_eq_chunked)
      (hzeroCandidates := block64ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
