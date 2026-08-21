import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 20

This block covers scan coordinates `[1000, 1050)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1000, 1050)`. -/
def block20ExpectedResidues_chunked : List (ZMod 12613) :=
  [8271, 9759, 12095, 3589, 4923, 3692, 10194, 5338, 1120, 11078,
    1990, 4431, 3725, 3635, 1806, 4596, 3016, 8305, 6755, 8048,
    8726, 8333, 8690, 10214, 11986, 2458, 6095, 11226, 11632, 11930,
    2125, 5960, 535, 6454, 2082, 9890, 11124, 3092, 5755, 7073,
    5969, 4103, 6413, 3446, 9534, 8090, 4337, 7023, 8152, 10759]

/-- The one batched computation certificate for block 20. -/
theorem scanBlockResidues_block20_eq_chunked :
    scanBlockResidues 1000 50 = block20ExpectedResidues_chunked := by
  decide

private theorem block20ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block20ExpectedResidues_chunked[i.val]'(by
        simp [block20ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1000 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 20 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block20_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1000 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1000 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1000) (width := 50) (hbound := by omega)
      (expected := block20ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block20_eq_chunked)
      (hzeroCandidates := block20ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
