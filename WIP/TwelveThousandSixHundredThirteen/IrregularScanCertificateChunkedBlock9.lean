import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 9

This block covers scan coordinates `[450, 500)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[450, 500)`. -/
def block9ExpectedResidues_chunked : List (ZMod 12613) :=
  [1036, 10666, 10694, 10884, 3302, 9038, 6714, 11224, 1157, 8290,
    4000, 9160, 3962, 9348, 8034, 3552, 7541, 3534, 12106, 4927,
    273, 6527, 6567, 5367, 11643, 10518, 316, 808, 11015, 3454,
    6, 3450, 4165, 1177, 12030, 11451, 1123, 321, 4867, 11124,
    6901, 12161, 8356, 12289, 1724, 8884, 6761, 6765, 9690, 3493]

/-- The one batched computation certificate for block 9. -/
theorem scanBlockResidues_block9_eq_chunked :
    scanBlockResidues 450 50 = block9ExpectedResidues_chunked := by
  decide

private theorem block9ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block9ExpectedResidues_chunked[i.val]'(by
        simp [block9ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 450 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 9 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block9_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 450 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 450 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 450) (width := 50) (hbound := by omega)
      (expected := block9ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block9_eq_chunked)
      (hzeroCandidates := block9ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
