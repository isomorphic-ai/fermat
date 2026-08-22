import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 21

This block covers scan coordinates `[1050, 1100)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1050, 1100)`. -/
def block21ExpectedResidues_chunked : List (ZMod 12613) :=
  [6857, 10582, 3187, 12288, 1090, 9042, 8710, 11911, 2283, 9677,
    6195, 6507, 10035, 10922, 7470, 5057, 11392, 12006, 11202, 3649,
    11129, 5260, 2987, 11695, 12411, 12251, 7527, 8913, 3181, 5493,
    12485, 4088, 5017, 12358, 8723, 12364, 238, 10176, 12327, 4280,
    4400, 3407, 9278, 4444, 6232, 7868, 544, 12266, 12467, 1902]

/-- The one batched computation certificate for block 21. -/
theorem scanBlockResidues_block21_eq_chunked :
    scanBlockResidues 1050 50 = block21ExpectedResidues_chunked := by
  decide

private theorem block21ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block21ExpectedResidues_chunked[i.val]'(by
        simp [block21ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1050 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 21 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block21_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1050 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1050 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1050) (width := 50) (hbound := by omega)
      (expected := block21ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block21_eq_chunked)
      (hzeroCandidates := block21ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
