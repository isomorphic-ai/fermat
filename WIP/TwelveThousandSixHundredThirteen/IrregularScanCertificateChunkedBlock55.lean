import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 55

This block covers scan coordinates `[2750, 2800)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2750, 2800)`. -/
def block55ExpectedResidues_chunked : List (ZMod 12613) :=
  [781, 9386, 5060, 2618, 3864, 223, 3030, 1493, 3637, 7268,
    11632, 10269, 1487, 12107, 1916, 8655, 8798, 10755, 3703, 6384,
    2416, 1709, 5607, 11129, 11688, 4507, 1485, 3675, 3507, 119,
    3160, 2956, 12019, 10037, 8070, 10833, 383, 7244, 2602, 8862,
    2484, 7055, 8751, 10195, 11389, 8950, 10113, 6977, 11841, 4112]

/-- The one batched computation certificate for block 55. -/
theorem scanBlockResidues_block55_eq_chunked :
    scanBlockResidues 2750 50 = block55ExpectedResidues_chunked := by
  decide

private theorem block55ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block55ExpectedResidues_chunked[i.val]'(by
        simp [block55ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2750 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 55 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block55_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2750 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2750 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2750) (width := 50) (hbound := by omega)
      (expected := block55ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block55_eq_chunked)
      (hzeroCandidates := block55ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
