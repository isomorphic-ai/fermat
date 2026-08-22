import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 106

This block covers scan coordinates `[5300, 5350)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5300, 5350)`. -/
def block106ExpectedResidues_chunked : List (ZMod 12613) :=
  [8074, 923, 7282, 11329, 5931, 132, 10700, 6596, 4752, 5381,
    9039, 4291, 6781, 8905, 3007, 2020, 2020, 11868, 3363, 4482,
    6596, 3357, 4807, 8015, 4690, 7307, 894, 572, 4646, 8613,
    4794, 5550, 8040, 2380, 11171, 2809, 4473, 9689, 1692, 2635,
    1059, 11285, 9334, 9401, 11481, 12482, 12531, 7606, 3979, 5788]

/-- The one batched computation certificate for block 106. -/
theorem scanBlockResidues_block106_eq_chunked :
    scanBlockResidues 5300 50 = block106ExpectedResidues_chunked := by
  decide

private theorem block106ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block106ExpectedResidues_chunked[i.val]'(by
        simp [block106ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5300 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 106 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block106_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5300 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5300 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5300) (width := 50) (hbound := by omega)
      (expected := block106ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block106_eq_chunked)
      (hzeroCandidates := block106ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
