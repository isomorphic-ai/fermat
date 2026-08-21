import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 115

This block covers scan coordinates `[5750, 5800)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5750, 5800)`. -/
def block115ExpectedResidues_chunked : List (ZMod 12613) :=
  [9839, 9387, 9953, 11307, 3221, 4337, 11352, 4753, 5757, 8284,
    8666, 7259, 8255, 10009, 10810, 5282, 2316, 8967, 4277, 1321,
    8572, 11837, 10407, 5797, 6926, 2356, 1455, 3252, 10278, 6068,
    8057, 5964, 4219, 7763, 3809, 12152, 9936, 1004, 11129, 7890,
    3544, 992, 10579, 10086, 10002, 7665, 7691, 4209, 12493, 8224]

/-- The one batched computation certificate for block 115. -/
theorem scanBlockResidues_block115_eq_chunked :
    scanBlockResidues 5750 50 = block115ExpectedResidues_chunked := by
  decide

private theorem block115ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block115ExpectedResidues_chunked[i.val]'(by
        simp [block115ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5750 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 115 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block115_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5750 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5750 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5750) (width := 50) (hbound := by omega)
      (expected := block115ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block115_eq_chunked)
      (hzeroCandidates := block115ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
