import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 27

This block covers scan coordinates `[1350, 1400)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1350, 1400)`. -/
def block27ExpectedResidues_chunked : List (ZMod 12613) :=
  [9215, 5319, 7408, 5968, 6089, 1646, 5039, 5768, 1433, 9486,
    6162, 8104, 2397, 4088, 9521, 7024, 12206, 9166, 6999, 7587,
    2054, 10542, 7934, 4809, 8276, 5013, 11217, 12349, 10044, 9305,
    1586, 7979, 11773, 11983, 5416, 4705, 6858, 4317, 8861, 463,
    11595, 3003, 9957, 7600, 10746, 7032, 9134, 9258, 7456, 9891]

/-- The one batched computation certificate for block 27. -/
theorem scanBlockResidues_block27_eq_chunked :
    scanBlockResidues 1350 50 = block27ExpectedResidues_chunked := by
  decide

private theorem block27ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block27ExpectedResidues_chunked[i.val]'(by
        simp [block27ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1350 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 27 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block27_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1350 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1350 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1350) (width := 50) (hbound := by omega)
      (expected := block27ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block27_eq_chunked)
      (hzeroCandidates := block27ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
