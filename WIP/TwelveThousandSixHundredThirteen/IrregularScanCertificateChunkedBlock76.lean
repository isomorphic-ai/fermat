import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 76

This block covers scan coordinates `[3800, 3850)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3800, 3850)`. -/
def block76ExpectedResidues_chunked : List (ZMod 12613) :=
  [9188, 10057, 9338, 827, 7911, 6901, 7830, 2497, 7628, 943,
    221, 8123, 6723, 11540, 11378, 1322, 5354, 10637, 3974, 3229,
    4283, 1866, 11851, 3322, 8828, 7724, 10372, 3140, 3103, 1479,
    11711, 9891, 6081, 8052, 887, 3523, 5668, 11667, 11010, 10672,
    11523, 2663, 3926, 3129, 3444, 11859, 9845, 8305, 9192, 9598]

/-- The one batched computation certificate for block 76. -/
theorem scanBlockResidues_block76_eq_chunked :
    scanBlockResidues 3800 50 = block76ExpectedResidues_chunked := by
  decide

private theorem block76ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block76ExpectedResidues_chunked[i.val]'(by
        simp [block76ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3800 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 76 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block76_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3800 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3800 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3800) (width := 50) (hbound := by omega)
      (expected := block76ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block76_eq_chunked)
      (hzeroCandidates := block76ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
