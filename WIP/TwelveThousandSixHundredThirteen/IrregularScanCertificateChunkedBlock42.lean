import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 42

This block covers scan coordinates `[2100, 2150)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2100, 2150)`. -/
def block42ExpectedResidues_chunked : List (ZMod 12613) :=
  [90, 6050, 7040, 9118, 11349, 4887, 1697, 5628, 7615, 1166,
    11206, 6195, 3544, 6415, 7821, 11236, 10049, 3812, 9442, 5848,
    6205, 4750, 1033, 2507, 2180, 12311, 10980, 9858, 5901, 676,
    8993, 9522, 6611, 5657, 3015, 10548, 4997, 2347, 2773, 3425,
    6625, 8270, 4497, 7218, 994, 5491, 5634, 2624, 8243, 2608]

/-- The one batched computation certificate for block 42. -/
theorem scanBlockResidues_block42_eq_chunked :
    scanBlockResidues 2100 50 = block42ExpectedResidues_chunked := by
  decide

private theorem block42ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block42ExpectedResidues_chunked[i.val]'(by
        simp [block42ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2100 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 42 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block42_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2100 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2100 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2100) (width := 50) (hbound := by omega)
      (expected := block42ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block42_eq_chunked)
      (hzeroCandidates := block42ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
