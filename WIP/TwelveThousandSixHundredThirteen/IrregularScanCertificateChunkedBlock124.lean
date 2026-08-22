import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 124

This block covers scan coordinates `[6200, 6250)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[6200, 6250)`. -/
def block124ExpectedResidues_chunked : List (ZMod 12613) :=
  [10561, 7520, 11511, 8976, 6045, 4492, 9073, 10527, 10656, 5045,
    636, 3179, 9509, 4949, 7272, 3110, 5506, 2654, 9546, 7716,
    2066, 9212, 6336, 745, 5584, 43, 3741, 9795, 8681, 3894,
    5843, 3684, 5696, 9590, 5154, 10946, 7260, 11108, 2482, 5807,
    1398, 1941, 6186, 2289, 4929, 11518, 3593, 6353, 12380, 6967]

/-- The one batched computation certificate for block 124. -/
theorem scanBlockResidues_block124_eq_chunked :
    scanBlockResidues 6200 50 = block124ExpectedResidues_chunked := by
  decide

private theorem block124ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block124ExpectedResidues_chunked[i.val]'(by
        simp [block124ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 6200 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 124 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block124_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 6200 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 6200 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 6200) (width := 50) (hbound := by omega)
      (expected := block124ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block124_eq_chunked)
      (hzeroCandidates := block124ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
