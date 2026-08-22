import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 126

This block covers scan coordinates `[6300, 6305)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[6300, 6305)`. -/
def block126ExpectedResidues_chunked : List (ZMod 12613) :=
  [11141, 3720, 459, 12453, 5776]

/-- The one batched computation certificate for block 126. -/
theorem scanBlockResidues_block126_eq_chunked :
    scanBlockResidues 6300 5 = block126ExpectedResidues_chunked := by
  decide

private theorem block126ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 5)
    (hzero :
      block126ExpectedResidues_chunked[i.val]'(by
        simp [block126ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 6300 5 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 126 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block126_chunked
    (i : Fin 5) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 6300 5 (by omega) i)) = 0 →
      scanIndex (offsetIndex 6300 5 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 6300) (width := 5) (hbound := by omega)
      (expected := block126ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block126_eq_chunked)
      (hzeroCandidates := block126ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
