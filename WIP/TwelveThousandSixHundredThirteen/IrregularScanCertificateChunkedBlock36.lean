import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 36

This block covers scan coordinates `[1800, 1850)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1800, 1850)`. -/
def block36ExpectedResidues_chunked : List (ZMod 12613) :=
  [9842, 650, 5456, 10977, 212, 2288, 7978, 1324, 10211, 5642,
    1047, 616, 9200, 3867, 4271, 5275, 204, 6529, 2618, 1233,
    3817, 2208, 10175, 4745, 6957, 8316, 10596, 12081, 7628, 6577,
    133, 2, 399, 6976, 10242, 5157, 12393, 12047, 4699, 10941,
    9388, 3713, 915, 5181, 5042, 6974, 7009, 12251, 5408, 1768]

/-- The one batched computation certificate for block 36. -/
theorem scanBlockResidues_block36_eq_chunked :
    scanBlockResidues 1800 50 = block36ExpectedResidues_chunked := by
  decide

private theorem block36ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block36ExpectedResidues_chunked[i.val]'(by
        simp [block36ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1800 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 36 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block36_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1800 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1800 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1800) (width := 50) (hbound := by omega)
      (expected := block36ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block36_eq_chunked)
      (hzeroCandidates := block36ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
