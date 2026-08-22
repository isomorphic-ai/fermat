import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 16

This block covers scan coordinates `[800, 850)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[800, 850)`. -/
def block16ExpectedResidues_chunked : List (ZMod 12613) :=
  [10129, 6358, 30, 9589, 3470, 8654, 5366, 7331, 1269, 11339,
    359, 12245, 1341, 10695, 5412, 879, 9372, 2460, 5848, 8348,
    6799, 12548, 4983, 5723, 11185, 715, 9223, 1521, 5428, 11560,
    7175, 6839, 10414, 10095, 1414, 12158, 4308, 11262, 9168, 8241,
    1438, 5734, 7185, 10610, 12588, 11978, 11269, 6367, 8149, 11501]

/-- The one batched computation certificate for block 16. -/
theorem scanBlockResidues_block16_eq_chunked :
    scanBlockResidues 800 50 = block16ExpectedResidues_chunked := by
  decide

private theorem block16ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block16ExpectedResidues_chunked[i.val]'(by
        simp [block16ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 800 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 16 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block16_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 800 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 800 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 800) (width := 50) (hbound := by omega)
      (expected := block16ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block16_eq_chunked)
      (hzeroCandidates := block16ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
