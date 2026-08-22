import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 111

This block covers scan coordinates `[5550, 5600)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5550, 5600)`. -/
def block111ExpectedResidues_chunked : List (ZMod 12613) :=
  [1261, 7912, 151, 1550, 8835, 9082, 2334, 8395, 11992, 8862,
    5877, 538, 11977, 8322, 3878, 10394, 11666, 11068, 4749, 6807,
    1401, 9152, 11605, 6620, 4718, 700, 10751, 2982, 1889, 8520,
    10664, 7305, 5399, 1616, 9132, 4677, 6427, 11382, 5537, 9580,
    2427, 6566, 2303, 6323, 4152, 10241, 2154, 10753, 5034, 6583]

/-- The one batched computation certificate for block 111. -/
theorem scanBlockResidues_block111_eq_chunked :
    scanBlockResidues 5550 50 = block111ExpectedResidues_chunked := by
  decide

private theorem block111ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block111ExpectedResidues_chunked[i.val]'(by
        simp [block111ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5550 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 111 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block111_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5550 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5550 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5550) (width := 50) (hbound := by omega)
      (expected := block111ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block111_eq_chunked)
      (hzeroCandidates := block111ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
