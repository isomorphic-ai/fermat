import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 80

This block covers scan coordinates `[4000, 4050)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4000, 4050)`. -/
def block80ExpectedResidues_chunked : List (ZMod 12613) :=
  [9635, 920, 8910, 6836, 9921, 3360, 638, 4866, 5870, 10243,
    9043, 11475, 8398, 10591, 3790, 8048, 453, 10135, 5688, 6321,
    6125, 6513, 4059, 360, 10397, 6498, 4586, 4228, 7391, 4749,
    910, 1096, 4489, 10024, 8884, 5574, 7696, 6192, 4441, 11139,
    1649, 2080, 6344, 5971, 2622, 6473, 1089, 1796, 8255, 3750]

/-- The one batched computation certificate for block 80. -/
theorem scanBlockResidues_block80_eq_chunked :
    scanBlockResidues 4000 50 = block80ExpectedResidues_chunked := by
  decide

private theorem block80ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block80ExpectedResidues_chunked[i.val]'(by
        simp [block80ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4000 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 80 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block80_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4000 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4000 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4000) (width := 50) (hbound := by omega)
      (expected := block80ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block80_eq_chunked)
      (hzeroCandidates := block80ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
