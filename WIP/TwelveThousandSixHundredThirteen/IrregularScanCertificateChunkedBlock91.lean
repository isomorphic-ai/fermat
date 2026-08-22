import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 91

This block covers scan coordinates `[4550, 4600)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4550, 4600)`. -/
def block91ExpectedResidues_chunked : List (ZMod 12613) :=
  [10691, 11481, 223, 9537, 5268, 8824, 7913, 10815, 5358, 11719,
    11240, 11784, 6058, 2671, 479, 675, 8207, 330, 11585, 284,
    7323, 11816, 3690, 12419, 600, 1025, 8263, 10333, 4048, 6776,
    6393, 558, 7412, 1069, 7572, 5633, 10290, 2081, 439, 10924,
    1761, 12088, 7681, 798, 4261, 877, 12564, 3783, 11713, 3116]

/-- The one batched computation certificate for block 91. -/
theorem scanBlockResidues_block91_eq_chunked :
    scanBlockResidues 4550 50 = block91ExpectedResidues_chunked := by
  decide

private theorem block91ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block91ExpectedResidues_chunked[i.val]'(by
        simp [block91ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4550 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 91 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block91_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4550 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4550 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4550) (width := 50) (hbound := by omega)
      (expected := block91ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block91_eq_chunked)
      (hzeroCandidates := block91ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
