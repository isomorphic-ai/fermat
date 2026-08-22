import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 22

This block covers scan coordinates `[1100, 1150)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1100, 1150)`. -/
def block22ExpectedResidues_chunked : List (ZMod 12613) :=
  [3638, 9233, 8163, 7491, 231, 3728, 3104, 4047, 440, 9404,
    2242, 12378, 1218, 9957, 2237, 2379, 4901, 438, 4973, 4678,
    12388, 420, 11734, 2746, 10886, 10418, 3135, 10769, 124, 40,
    6636, 6529, 12399, 5905, 1584, 10112, 7510, 9398, 4472, 2798,
    2283, 6204, 988, 10649, 1931, 8732, 10617, 11564, 9099, 7758]

/-- The one batched computation certificate for block 22. -/
theorem scanBlockResidues_block22_eq_chunked :
    scanBlockResidues 1100 50 = block22ExpectedResidues_chunked := by
  decide

private theorem block22ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block22ExpectedResidues_chunked[i.val]'(by
        simp [block22ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1100 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 22 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block22_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1100 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1100 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1100) (width := 50) (hbound := by omega)
      (expected := block22ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block22_eq_chunked)
      (hzeroCandidates := block22ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
