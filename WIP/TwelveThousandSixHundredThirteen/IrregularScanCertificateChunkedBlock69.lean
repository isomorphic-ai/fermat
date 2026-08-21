import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 69

This block covers scan coordinates `[3450, 3500)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3450, 3500)`. -/
def block69ExpectedResidues_chunked : List (ZMod 12613) :=
  [12548, 7116, 5455, 3813, 1285, 11857, 7204, 6231, 2139, 10099,
    5096, 11573, 8417, 4496, 2434, 2386, 5424, 2796, 1956, 6677,
    1704, 8091, 7372, 4312, 7403, 7147, 11067, 1521, 4546, 42,
    2609, 5852, 9630, 320, 4364, 4813, 7959, 8410, 11232, 6295,
    2632, 2844, 3655, 8461, 11738, 5686, 9544, 6068, 1848, 11461]

/-- The one batched computation certificate for block 69. -/
theorem scanBlockResidues_block69_eq_chunked :
    scanBlockResidues 3450 50 = block69ExpectedResidues_chunked := by
  decide

private theorem block69ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block69ExpectedResidues_chunked[i.val]'(by
        simp [block69ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3450 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 69 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block69_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3450 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3450 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3450) (width := 50) (hbound := by omega)
      (expected := block69ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block69_eq_chunked)
      (hzeroCandidates := block69ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
