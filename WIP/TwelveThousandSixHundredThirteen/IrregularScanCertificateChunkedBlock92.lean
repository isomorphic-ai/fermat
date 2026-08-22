import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 92

This block covers scan coordinates `[4600, 4650)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4600, 4650)`. -/
def block92ExpectedResidues_chunked : List (ZMod 12613) :=
  [41, 6325, 5180, 9117, 2193, 1058, 3659, 7492, 5240, 12559,
    7096, 6406, 1026, 5155, 3986, 10625, 10879, 6278, 9437, 6489,
    11811, 69, 213, 4592, 5412, 11006, 6809, 49, 6795, 62,
    918, 5197, 3062, 9627, 10756, 9823, 1397, 3220, 383, 7532,
    2955, 6965, 438, 10040, 12484, 1649, 963, 547, 7815, 12593]

/-- The one batched computation certificate for block 92. -/
theorem scanBlockResidues_block92_eq_chunked :
    scanBlockResidues 4600 50 = block92ExpectedResidues_chunked := by
  decide

private theorem block92ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block92ExpectedResidues_chunked[i.val]'(by
        simp [block92ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4600 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 92 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block92_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4600 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4600 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4600) (width := 50) (hbound := by omega)
      (expected := block92ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block92_eq_chunked)
      (hzeroCandidates := block92ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
