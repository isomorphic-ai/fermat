import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 70

This block covers scan coordinates `[3500, 3550)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3500, 3550)`. -/
def block70ExpectedResidues_chunked : List (ZMod 12613) :=
  [5709, 2014, 5612, 11651, 9046, 4240, 5978, 1827, 8572, 2727,
    1957, 5093, 10997, 6430, 1897, 3260, 3805, 2074, 2723, 3999,
    5483, 6951, 7400, 11947, 11044, 4116, 4723, 8675, 6736, 5159,
    5339, 1649, 986, 5748, 11944, 1142, 5677, 4375, 3559, 845,
    6260, 3818, 4588, 9221, 8803, 3705, 9591, 2481, 5814, 10031]

/-- The one batched computation certificate for block 70. -/
theorem scanBlockResidues_block70_eq_chunked :
    scanBlockResidues 3500 50 = block70ExpectedResidues_chunked := by
  decide

private theorem block70ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block70ExpectedResidues_chunked[i.val]'(by
        simp [block70ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3500 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 70 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block70_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3500 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3500 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3500) (width := 50) (hbound := by omega)
      (expected := block70ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block70_eq_chunked)
      (hzeroCandidates := block70ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
