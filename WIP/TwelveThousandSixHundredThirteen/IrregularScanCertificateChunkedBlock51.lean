import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 51

This block covers scan coordinates `[2550, 2600)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2550, 2600)`. -/
def block51ExpectedResidues_chunked : List (ZMod 12613) :=
  [4306, 3529, 3642, 6315, 6144, 611, 1470, 6949, 5920, 8017,
    10150, 11212, 10582, 5036, 2274, 1586, 10983, 8769, 5102, 6828,
    4575, 10178, 5625, 9186, 3817, 3768, 8777, 12547, 3922, 3335,
    11112, 9636, 8711, 7913, 4100, 3445, 1434, 5694, 10144, 9821,
    2528, 9935, 12598, 6374, 4724, 1283, 10566, 8129, 7960, 2156]

/-- The one batched computation certificate for block 51. -/
theorem scanBlockResidues_block51_eq_chunked :
    scanBlockResidues 2550 50 = block51ExpectedResidues_chunked := by
  decide

private theorem block51ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block51ExpectedResidues_chunked[i.val]'(by
        simp [block51ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2550 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 51 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block51_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2550 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2550 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2550) (width := 50) (hbound := by omega)
      (expected := block51ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block51_eq_chunked)
      (hzeroCandidates := block51ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
