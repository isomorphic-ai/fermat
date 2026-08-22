import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 110

This block covers scan coordinates `[5500, 5550)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5500, 5550)`. -/
def block110ExpectedResidues_chunked : List (ZMod 12613) :=
  [10081, 7369, 7891, 7578, 2969, 6793, 4970, 6395, 4871, 4478,
    4901, 10403, 9982, 12558, 2754, 3005, 3236, 11499, 3028, 10762,
    4871, 1129, 6365, 12588, 10612, 7201, 11289, 11753, 8896, 7958,
    3280, 11629, 3439, 6271, 9428, 9022, 7071, 10287, 4222, 3762,
    2294, 1010, 2977, 1029, 4532, 2637, 1155, 3498, 3900, 7553]

/-- The one batched computation certificate for block 110. -/
theorem scanBlockResidues_block110_eq_chunked :
    scanBlockResidues 5500 50 = block110ExpectedResidues_chunked := by
  decide

private theorem block110ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block110ExpectedResidues_chunked[i.val]'(by
        simp [block110ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5500 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 110 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block110_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5500 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5500 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5500) (width := 50) (hbound := by omega)
      (expected := block110ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block110_eq_chunked)
      (hzeroCandidates := block110ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
