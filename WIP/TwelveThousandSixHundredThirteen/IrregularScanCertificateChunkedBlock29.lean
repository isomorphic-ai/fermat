import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 29

This block covers scan coordinates `[1450, 1500)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1450, 1500)`. -/
def block29ExpectedResidues_chunked : List (ZMod 12613) :=
  [8263, 9234, 3471, 9201, 11735, 9453, 3945, 332, 7360, 3875,
    670, 2861, 7941, 8269, 1578, 10926, 3160, 3236, 8622, 1630,
    5247, 9150, 9279, 3515, 6295, 10626, 2971, 7276, 10776, 3479,
    10691, 2765, 1308, 8415, 1266, 1819, 1183, 10664, 374, 12246,
    302, 859, 137, 7806, 6782, 5077, 10982, 4217, 3418, 9600]

/-- The one batched computation certificate for block 29. -/
theorem scanBlockResidues_block29_eq_chunked :
    scanBlockResidues 1450 50 = block29ExpectedResidues_chunked := by
  decide

private theorem block29ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block29ExpectedResidues_chunked[i.val]'(by
        simp [block29ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1450 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 29 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block29_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1450 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1450 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1450) (width := 50) (hbound := by omega)
      (expected := block29ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block29_eq_chunked)
      (hzeroCandidates := block29ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
