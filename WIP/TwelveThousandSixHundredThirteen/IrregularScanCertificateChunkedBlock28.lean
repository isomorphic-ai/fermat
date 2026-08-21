import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 28

This block covers scan coordinates `[1400, 1450)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1400, 1450)`. -/
def block28ExpectedResidues_chunked : List (ZMod 12613) :=
  [10959, 6964, 7470, 10648, 9513, 11447, 6389, 6442, 2956, 7704,
    3755, 2577, 2926, 4795, 9348, 11598, 822, 10391, 8699, 8983,
    3480, 10866, 9169, 9950, 11865, 12170, 513, 10713, 1152, 10390,
    9543, 3179, 3135, 7803, 6186, 5943, 3914, 8508, 11822, 1251,
    11872, 8297, 578, 2088, 8034, 6625, 8826, 6778, 8056, 878]

/-- The one batched computation certificate for block 28. -/
theorem scanBlockResidues_block28_eq_chunked :
    scanBlockResidues 1400 50 = block28ExpectedResidues_chunked := by
  decide

private theorem block28ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block28ExpectedResidues_chunked[i.val]'(by
        simp [block28ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1400 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 28 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block28_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1400 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1400 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1400) (width := 50) (hbound := by omega)
      (expected := block28ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block28_eq_chunked)
      (hzeroCandidates := block28ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
