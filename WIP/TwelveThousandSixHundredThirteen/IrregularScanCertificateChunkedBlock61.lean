import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 61

This block covers scan coordinates `[3050, 3100)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3050, 3100)`. -/
def block61ExpectedResidues_chunked : List (ZMod 12613) :=
  [11649, 10608, 1339, 11830, 909, 3282, 3167, 6553, 5106, 3410,
    10796, 1634, 10218, 4277, 9354, 4368, 10692, 6507, 10774, 2530,
    11571, 7502, 998, 8666, 3034, 5283, 2350, 11540, 9969, 4614,
    11106, 2043, 10560, 3553, 2652, 2763, 8415, 6642, 4807, 1130,
    2265, 4194, 7451, 11878, 4318, 2701, 4234, 8417, 12593, 577]

/-- The one batched computation certificate for block 61. -/
theorem scanBlockResidues_block61_eq_chunked :
    scanBlockResidues 3050 50 = block61ExpectedResidues_chunked := by
  decide

private theorem block61ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block61ExpectedResidues_chunked[i.val]'(by
        simp [block61ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3050 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 61 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block61_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3050 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3050 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3050) (width := 50) (hbound := by omega)
      (expected := block61ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block61_eq_chunked)
      (hzeroCandidates := block61ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
