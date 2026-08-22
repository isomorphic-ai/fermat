import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 95

This block covers scan coordinates `[4750, 4800)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4750, 4800)`. -/
def block95ExpectedResidues_chunked : List (ZMod 12613) :=
  [7585, 9141, 4803, 12385, 3821, 297, 10975, 2385, 11576, 6194,
    1897, 8090, 1416, 4511, 3759, 12592, 6622, 8538, 7459, 4779,
    11758, 8741, 8881, 8736, 12564, 4332, 11703, 4154, 10587, 10818,
    9980, 2562, 3948, 10297, 7339, 11885, 2496, 3362, 11638, 10652,
    4886, 4924, 2192, 3964, 2042, 12284, 10127, 12523, 1510, 10845]

/-- The one batched computation certificate for block 95. -/
theorem scanBlockResidues_block95_eq_chunked :
    scanBlockResidues 4750 50 = block95ExpectedResidues_chunked := by
  decide

private theorem block95ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block95ExpectedResidues_chunked[i.val]'(by
        simp [block95ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4750 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 95 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block95_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4750 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4750 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4750) (width := 50) (hbound := by omega)
      (expected := block95ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block95_eq_chunked)
      (hzeroCandidates := block95ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
