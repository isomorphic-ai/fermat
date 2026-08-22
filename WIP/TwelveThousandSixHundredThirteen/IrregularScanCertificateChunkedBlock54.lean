import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 54

This block covers scan coordinates `[2700, 2750)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2700, 2750)`. -/
def block54ExpectedResidues_chunked : List (ZMod 12613) :=
  [2283, 2898, 4668, 8880, 9784, 5572, 5696, 583, 8039, 2039,
    3540, 1777, 6205, 12077, 12360, 4467, 5702, 1607, 10263, 8641,
    7109, 55, 4841, 1683, 2215, 12053, 7056, 7108, 10814, 12366,
    728, 4662, 2351, 1248, 11210, 5815, 5203, 10598, 10767, 10434,
    7650, 754, 4261, 12371, 6377, 7229, 8080, 6107, 1638, 3658]

/-- The one batched computation certificate for block 54. -/
theorem scanBlockResidues_block54_eq_chunked :
    scanBlockResidues 2700 50 = block54ExpectedResidues_chunked := by
  decide

private theorem block54ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block54ExpectedResidues_chunked[i.val]'(by
        simp [block54ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2700 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 54 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block54_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2700 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2700 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2700) (width := 50) (hbound := by omega)
      (expected := block54ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block54_eq_chunked)
      (hzeroCandidates := block54ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
