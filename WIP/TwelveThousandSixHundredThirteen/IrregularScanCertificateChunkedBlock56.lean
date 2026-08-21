import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 56

This block covers scan coordinates `[2800, 2850)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2800, 2850)`. -/
def block56ExpectedResidues_chunked : List (ZMod 12613) :=
  [8953, 7030, 2944, 11580, 6350, 6847, 8777, 1247, 9371, 8611,
    11099, 2328, 3941, 3192, 2838, 12415, 1366, 10931, 11047, 10775,
    6795, 1015, 10887, 3100, 4642, 173, 3502, 8505, 2168, 8482,
    2621, 6728, 10809, 8143, 10278, 1332, 5728, 12247, 3219, 6479,
    8723, 239, 5944, 7810, 1473, 5770, 11862, 3661, 6421, 7696]

/-- The one batched computation certificate for block 56. -/
theorem scanBlockResidues_block56_eq_chunked :
    scanBlockResidues 2800 50 = block56ExpectedResidues_chunked := by
  decide

private theorem block56ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block56ExpectedResidues_chunked[i.val]'(by
        simp [block56ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2800 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 56 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block56_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2800 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2800 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2800) (width := 50) (hbound := by omega)
      (expected := block56ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block56_eq_chunked)
      (hzeroCandidates := block56ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
