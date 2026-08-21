import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 79

This block covers scan coordinates `[3950, 4000)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3950, 4000)`. -/
def block79ExpectedResidues_chunked : List (ZMod 12613) :=
  [6436, 331, 7523, 3077, 5893, 3535, 6527, 2797, 10621, 6746,
    200, 3541, 519, 5230, 1479, 4232, 11625, 4767, 6826, 6227,
    5430, 8806, 1695, 10392, 11214, 6528, 9363, 909, 8861, 3321,
    10011, 3827, 4344, 10313, 2358, 11637, 4003, 9243, 7822, 7146,
    7297, 11931, 11928, 11714, 1472, 5023, 11943, 4766, 2295, 7894]

/-- The one batched computation certificate for block 79. -/
theorem scanBlockResidues_block79_eq_chunked :
    scanBlockResidues 3950 50 = block79ExpectedResidues_chunked := by
  decide

private theorem block79ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block79ExpectedResidues_chunked[i.val]'(by
        simp [block79ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3950 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 79 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block79_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3950 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3950 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3950) (width := 50) (hbound := by omega)
      (expected := block79ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block79_eq_chunked)
      (hzeroCandidates := block79ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
