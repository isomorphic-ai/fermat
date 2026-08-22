import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 100

This block covers scan coordinates `[5000, 5050)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5000, 5050)`. -/
def block100ExpectedResidues_chunked : List (ZMod 12613) :=
  [10747, 4889, 9116, 4868, 11794, 9669, 11440, 1198, 8902, 7539,
    6375, 2912, 10106, 7764, 11751, 7141, 1376, 635, 3226, 5582,
    3704, 7530, 7583, 698, 3904, 10826, 4487, 11429, 2009, 4739,
    6265, 5309, 11523, 5514, 8115, 6747, 4538, 4698, 1050, 8753,
    11953, 10404, 8954, 237, 291, 960, 10242, 2930, 1438, 10878]

/-- The one batched computation certificate for block 100. -/
theorem scanBlockResidues_block100_eq_chunked :
    scanBlockResidues 5000 50 = block100ExpectedResidues_chunked := by
  decide

private theorem block100ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block100ExpectedResidues_chunked[i.val]'(by
        simp [block100ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5000 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 100 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block100_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5000 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5000 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5000) (width := 50) (hbound := by omega)
      (expected := block100ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block100_eq_chunked)
      (hzeroCandidates := block100ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
