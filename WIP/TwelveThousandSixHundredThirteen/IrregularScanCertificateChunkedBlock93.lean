import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 93

This block covers scan coordinates `[4650, 4700)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4650, 4700)`. -/
def block93ExpectedResidues_chunked : List (ZMod 12613) :=
  [12161, 10006, 8537, 10740, 11200, 6166, 6293, 10119, 2619, 634,
    5663, 4364, 9851, 7306, 6608, 7154, 1315, 1147, 10933, 1863,
    7553, 768, 8566, 12135, 4096, 7950, 9343, 10078, 2077, 2285,
    5441, 11445, 8213, 11116, 3094, 1715, 7624, 8265, 3939, 2525,
    2151, 936, 9137, 9174, 126, 4610, 12430, 9079, 4938, 0]

/-- The one batched computation certificate for block 93. -/
theorem scanBlockResidues_block93_eq_chunked :
    scanBlockResidues 4650 50 = block93ExpectedResidues_chunked := by
  decide

private theorem block93ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block93ExpectedResidues_chunked[i.val]'(by
        simp [block93ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4650 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 93 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block93_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4650 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4650 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4650) (width := 50) (hbound := by omega)
      (expected := block93ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block93_eq_chunked)
      (hzeroCandidates := block93ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
