import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 116

This block covers scan coordinates `[5800, 5850)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5800, 5850)`. -/
def block116ExpectedResidues_chunked : List (ZMod 12613) :=
  [7106, 4791, 12212, 1202, 2300, 578, 3247, 1769, 5443, 10945,
    1641, 1423, 3963, 7493, 12182, 6721, 171, 1934, 18, 10921,
    7652, 5162, 8517, 12106, 2100, 6010, 6287, 1758, 9243, 4103,
    8244, 1783, 5922, 7178, 11002, 11899, 7697, 11560, 7265, 1058,
    4596, 1285, 12571, 3883, 10128, 4892, 8297, 3518, 6932, 3709]

/-- The one batched computation certificate for block 116. -/
theorem scanBlockResidues_block116_eq_chunked :
    scanBlockResidues 5800 50 = block116ExpectedResidues_chunked := by
  decide

private theorem block116ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block116ExpectedResidues_chunked[i.val]'(by
        simp [block116ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5800 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 116 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block116_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5800 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5800 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5800) (width := 50) (hbound := by omega)
      (expected := block116ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block116_eq_chunked)
      (hzeroCandidates := block116ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
