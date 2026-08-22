import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 11

This block covers scan coordinates `[550, 600)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[550, 600)`. -/
def block11ExpectedResidues_chunked : List (ZMod 12613) :=
  [5258, 9851, 4261, 3031, 5011, 3388, 426, 4580, 1634, 2757,
    9305, 1675, 5333, 9050, 2684, 1519, 1309, 11557, 1145, 5048,
    3237, 9465, 4923, 11947, 11652, 7340, 5482, 7203, 1636, 5490,
    7025, 4666, 6875, 6700, 6730, 7280, 12477, 7244, 7794, 747,
    794, 11647, 12528, 8449, 11255, 9998, 7758, 9360, 791, 2752]

/-- The one batched computation certificate for block 11. -/
theorem scanBlockResidues_block11_eq_chunked :
    scanBlockResidues 550 50 = block11ExpectedResidues_chunked := by
  decide

private theorem block11ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block11ExpectedResidues_chunked[i.val]'(by
        simp [block11ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 550 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 11 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block11_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 550 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 550 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 550) (width := 50) (hbound := by omega)
      (expected := block11ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block11_eq_chunked)
      (hzeroCandidates := block11ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
