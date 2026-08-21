import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 125

This block covers scan coordinates `[6250, 6300)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[6250, 6300)`. -/
def block125ExpectedResidues_chunked : List (ZMod 12613) :=
  [3205, 11475, 2227, 372, 10439, 3023, 2027, 5923, 2552, 4403,
    4983, 11680, 10981, 7679, 12444, 8068, 12404, 3145, 1438, 8697,
    4511, 11892, 3728, 8424, 7094, 436, 6250, 9034, 3644, 4589,
    1439, 110, 8980, 5883, 7893, 3552, 3227, 6945, 10385, 5125,
    6791, 2577, 9996, 1337, 4389, 578, 10484, 3441, 11276, 2318]

/-- The one batched computation certificate for block 125. -/
theorem scanBlockResidues_block125_eq_chunked :
    scanBlockResidues 6250 50 = block125ExpectedResidues_chunked := by
  decide

private theorem block125ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block125ExpectedResidues_chunked[i.val]'(by
        simp [block125ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 6250 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 125 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block125_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 6250 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 6250 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 6250) (width := 50) (hbound := by omega)
      (expected := block125ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block125_eq_chunked)
      (hzeroCandidates := block125ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
