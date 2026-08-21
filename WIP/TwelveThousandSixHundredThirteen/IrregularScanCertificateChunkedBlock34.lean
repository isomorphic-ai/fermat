import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 34

This block covers scan coordinates `[1700, 1750)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1700, 1750)`. -/
def block34ExpectedResidues_chunked : List (ZMod 12613) :=
  [10307, 9690, 11967, 11040, 1496, 9612, 9307, 11689, 9313, 3379,
    1996, 5486, 5450, 1000, 6506, 11687, 8714, 12426, 3948, 5768,
    1429, 4080, 5824, 11211, 5829, 9251, 5550, 10463, 4879, 2203,
    4273, 6396, 12356, 2349, 2295, 3276, 10512, 221, 3629, 1048,
    8694, 1583, 11067, 662, 5947, 3925, 6864, 2875, 2046, 5418]

/-- The one batched computation certificate for block 34. -/
theorem scanBlockResidues_block34_eq_chunked :
    scanBlockResidues 1700 50 = block34ExpectedResidues_chunked := by
  decide

private theorem block34ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block34ExpectedResidues_chunked[i.val]'(by
        simp [block34ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1700 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 34 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block34_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1700 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1700 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1700) (width := 50) (hbound := by omega)
      (expected := block34ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block34_eq_chunked)
      (hzeroCandidates := block34ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
