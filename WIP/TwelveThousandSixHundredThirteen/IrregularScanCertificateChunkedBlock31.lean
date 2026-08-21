import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 31

This block covers scan coordinates `[1550, 1600)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1550, 1600)`. -/
def block31ExpectedResidues_chunked : List (ZMod 12613) :=
  [864, 6890, 7064, 2837, 1150, 12349, 3295, 1499, 581, 891,
    4287, 8117, 4807, 885, 3793, 505, 3418, 11771, 149, 4778,
    2461, 12142, 9875, 11796, 268, 2308, 7075, 2805, 433, 2979,
    8363, 10232, 7598, 9912, 10154, 7903, 4744, 9337, 5613, 6225,
    5080, 5886, 2115, 7402, 7369, 9440, 6165, 11126, 238, 173]

/-- The one batched computation certificate for block 31. -/
theorem scanBlockResidues_block31_eq_chunked :
    scanBlockResidues 1550 50 = block31ExpectedResidues_chunked := by
  decide

private theorem block31ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block31ExpectedResidues_chunked[i.val]'(by
        simp [block31ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1550 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 31 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block31_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1550 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1550 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1550) (width := 50) (hbound := by omega)
      (expected := block31ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block31_eq_chunked)
      (hzeroCandidates := block31ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
