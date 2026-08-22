import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 71

This block covers scan coordinates `[3550, 3600)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3550, 3600)`. -/
def block71ExpectedResidues_chunked : List (ZMod 12613) :=
  [5597, 7065, 6837, 7414, 3168, 6698, 6865, 11600, 1800, 11807,
    12536, 5057, 2571, 7626, 7868, 9974, 2325, 2075, 9748, 11378,
    7651, 2057, 382, 4142, 9059, 11224, 1458, 1324, 6272, 4866,
    2347, 1816, 4195, 6795, 9119, 8643, 1201, 9277, 281, 1488,
    8248, 3004, 2896, 12292, 2496, 8245, 9502, 9623, 8203, 12523]

/-- The one batched computation certificate for block 71. -/
theorem scanBlockResidues_block71_eq_chunked :
    scanBlockResidues 3550 50 = block71ExpectedResidues_chunked := by
  decide

private theorem block71ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block71ExpectedResidues_chunked[i.val]'(by
        simp [block71ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3550 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 71 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block71_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3550 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3550 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3550) (width := 50) (hbound := by omega)
      (expected := block71ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block71_eq_chunked)
      (hzeroCandidates := block71ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
