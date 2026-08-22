import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 118

This block covers scan coordinates `[5900, 5950)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5900, 5950)`. -/
def block118ExpectedResidues_chunked : List (ZMod 12613) :=
  [11477, 280, 4435, 3131, 11242, 11487, 7681, 3535, 2849, 472,
    3909, 7574, 10990, 4570, 8569, 2613, 2831, 8202, 9385, 3581,
    11691, 8371, 2957, 2421, 8785, 10091, 8764, 10657, 10826, 5846,
    10785, 6773, 9370, 9665, 11317, 1758, 12022, 7001, 3147, 5762,
    6976, 7401, 842, 1783, 6253, 8891, 8241, 5070, 5153, 8517]

/-- The one batched computation certificate for block 118. -/
theorem scanBlockResidues_block118_eq_chunked :
    scanBlockResidues 5900 50 = block118ExpectedResidues_chunked := by
  decide

private theorem block118ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block118ExpectedResidues_chunked[i.val]'(by
        simp [block118ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5900 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 118 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block118_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5900 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5900 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5900) (width := 50) (hbound := by omega)
      (expected := block118ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block118_eq_chunked)
      (hzeroCandidates := block118ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
