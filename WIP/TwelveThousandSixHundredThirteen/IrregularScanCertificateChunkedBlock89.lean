import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 89

This block covers scan coordinates `[4450, 4500)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4450, 4500)`. -/
def block89ExpectedResidues_chunked : List (ZMod 12613) :=
  [8748, 8215, 3454, 12185, 9608, 10739, 931, 9160, 2153, 9444,
    10104, 5405, 9337, 2717, 5776, 11328, 11478, 9175, 10317, 10605,
    9352, 3137, 10180, 4305, 8648, 9921, 4659, 2611, 1719, 11760,
    5922, 10973, 3675, 11544, 1554, 1556, 1475, 8930, 3458, 5160,
    5354, 2359, 6513, 316, 10137, 3241, 3038, 7070, 7933, 1791]

/-- The one batched computation certificate for block 89. -/
theorem scanBlockResidues_block89_eq_chunked :
    scanBlockResidues 4450 50 = block89ExpectedResidues_chunked := by
  decide

private theorem block89ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block89ExpectedResidues_chunked[i.val]'(by
        simp [block89ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4450 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 89 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block89_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4450 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4450 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4450) (width := 50) (hbound := by omega)
      (expected := block89ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block89_eq_chunked)
      (hzeroCandidates := block89ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
