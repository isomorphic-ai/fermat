import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 32

This block covers scan coordinates `[1600, 1650)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1600, 1650)`. -/
def block32ExpectedResidues_chunked : List (ZMod 12613) :=
  [9078, 8980, 5582, 6322, 1526, 3947, 722, 11769, 975, 10582,
    1845, 7244, 1176, 2619, 4599, 7533, 548, 7059, 2426, 5883,
    939, 3074, 6837, 8312, 3803, 6735, 11211, 1873, 10438, 2828,
    4248, 11018, 11106, 2873, 1876, 11851, 7824, 10679, 8091, 11611,
    373, 2674, 12011, 10436, 9917, 6087, 6219, 2213, 11313, 659]

/-- The one batched computation certificate for block 32. -/
theorem scanBlockResidues_block32_eq_chunked :
    scanBlockResidues 1600 50 = block32ExpectedResidues_chunked := by
  decide

private theorem block32ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block32ExpectedResidues_chunked[i.val]'(by
        simp [block32ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1600 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 32 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block32_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1600 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1600 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1600) (width := 50) (hbound := by omega)
      (expected := block32ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block32_eq_chunked)
      (hzeroCandidates := block32ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
