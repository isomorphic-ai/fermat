import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 97

This block covers scan coordinates `[4850, 4900)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4850, 4900)`. -/
def block97ExpectedResidues_chunked : List (ZMod 12613) :=
  [1251, 9090, 6881, 165, 1268, 4772, 1497, 7295, 1317, 4079,
    8409, 9250, 6054, 9222, 3847, 2124, 25, 5255, 1676, 12323,
    4354, 12019, 2083, 6032, 7428, 3369, 11228, 7541, 4805, 7008,
    12498, 5355, 2166, 2155, 4740, 2638, 5299, 5040, 221, 4337,
    4824, 4095, 1507, 7712, 4655, 1043, 2247, 533, 4483, 20]

/-- The one batched computation certificate for block 97. -/
theorem scanBlockResidues_block97_eq_chunked :
    scanBlockResidues 4850 50 = block97ExpectedResidues_chunked := by
  decide

private theorem block97ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block97ExpectedResidues_chunked[i.val]'(by
        simp [block97ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4850 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 97 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block97_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4850 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4850 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4850) (width := 50) (hbound := by omega)
      (expected := block97ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block97_eq_chunked)
      (hzeroCandidates := block97ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
